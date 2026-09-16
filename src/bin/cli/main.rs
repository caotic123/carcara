mod app;
mod benchmarking;
mod error;
mod logger;
mod path_args;

use app::*;
use carcara::{
    ast::{self, Proof, rare_rules::Rules},
    benchmarking::OnlineBenchmarkResults,
    check, check_and_elaborate, check_parallel, generate_lia_smt_instances, parser, slice,
    translation::{self, ProofPrinter, Translator},
};
use error::{CliError, CliResult};
use path_args::{get_instances_from_paths, infer_problem_path};
use std::{
    fs::File,
    io::{self, IsTerminal, Read, Write},
    path::PathBuf,
    sync::atomic,
};

use clap::Parser;

fn main() {
    // The recursive-descent parser needs a few (debug-build) frames per
    // nesting level, and real proofs nest hundreds of levels deep — past the
    // main thread's default stack.  The CLI runs on a thread with room.
    const STACK_SIZE: usize = 512 * 1024 * 1024;
    let cli = std::thread::Builder::new()
        .stack_size(STACK_SIZE)
        .spawn(run_cli)
        .expect("failed to spawn the CLI thread");
    if cli.join().is_err() {
        std::process::exit(101);
    }
}

fn run_cli() {
    let cli = Cli::parse();
    let colors_enabled = !cli.no_color && std::io::stderr().is_terminal();

    ast::printer::USE_SHARING_IN_TERM_DISPLAY
        .store(!cli.no_print_with_sharing, atomic::Ordering::Relaxed);

    logger::init(cli.log_level.into(), colors_enabled);

    let result = match cli.command {
        Command::Parse(options) => parse_command(options).and_then(|(pb, pf, _rules, mut pool)| {
            ast::printer::print_proof(&mut pool, &pb.prelude, &pf, !cli.no_print_with_sharing)?;
            Ok(())
        }),
        Command::Check(options) => {
            match check_command(options) {
                Ok(s) => println!("{}", s),
                Err(e) => {
                    log::error!("{}", e);
                    println!("invalid");
                    std::process::exit(1);
                }
            }
            return;
        }
        Command::Elaborate(options) => {
            elaborate_command(options).and_then(|(res, pb, pf, mut pool)| {
                println!("{}", res);
                ast::printer::print_proof(&mut pool, &pb.prelude, &pf, !cli.no_print_with_sharing)?;
                Ok(())
            })
        }
        Command::Bench(options) => bench_command(options),
        Command::Slice(options) => {
            slice_command(options, cli.no_print_with_sharing).and_then(|(pb, pf, mut pool)| {
                ast::printer::print_proof(&mut pool, &pb.prelude, &pf, !cli.no_print_with_sharing)?;
                Ok(())
            })
        }
        Command::GenerateLiaProblems(options) => {
            generate_lia_problems_command(options, !cli.no_print_with_sharing)
        }
        Command::Translate(options) => translate_command(options),
        Command::ReconstructHole(options) => reconstruct_hole_command(options),
    };
    if let Err(e) = result {
        log::error!("{}", e);
        std::process::exit(1);
    }
}

struct Instance {
    problem: (PathBuf, String),
    proof: (PathBuf, String),
    rules: Option<(PathBuf, String)>,
}

impl Instance {
    fn problem(&self) -> parser::Source<'_> {
        parser::Source::new(&self.problem.0, &self.problem.1)
    }

    fn proof(&self) -> parser::Source<'_> {
        parser::Source::new(&self.proof.0, &self.proof.1)
    }

    fn rules(&self) -> Option<parser::Source<'_>> {
        let (name, contents) = self.rules.as_ref()?;
        Some(parser::Source::new(name, contents))
    }
}

fn get_instance(options: &Input) -> CliResult<Instance> {
    let file_source = |path: &str| -> Result<(PathBuf, String), carcara::Error> {
        let contents = std::fs::read_to_string(path)
            .map_err(|e| carcara::Error::Io { inner: e, file: path.into() })?;
        Ok((path.into(), contents))
    };
    let stdin_source = || -> Result<(PathBuf, String), carcara::Error> {
        let mut buf = String::new();
        io::stdin()
            .read_to_string(&mut buf)
            .map_err(|e| carcara::Error::Io { inner: e, file: "<stdin>".into() })?;
        Ok(("<stdin>".into(), buf))
    };

    let (problem, proof) = match (options.problem_file.as_deref(), options.proof_file.as_str()) {
        (Some("-"), "-") | (None, "-") => return Err(CliError::BothFilesStdin),
        (Some(problem), "-") => (file_source(problem)?, stdin_source()?),
        (Some("-"), proof) => (stdin_source()?, file_source(proof)?),
        (Some(problem), proof) => (file_source(problem)?, file_source(proof)?),
        (None, proof) => {
            let problem = infer_problem_path(proof)?;
            (file_source(problem.to_str().unwrap())?, file_source(proof)?)
        }
    };
    let rules = options
        .rare_file
        .as_ref()
        .map(|f| file_source(f))
        .transpose()?;

    Ok(Instance { problem, proof, rules })
}

fn parse_command(
    options: ParseCommandOptions,
) -> CliResult<(ast::Problem, ast::Proof, Rules, ast::pool::PrimitivePool)> {
    let instance = get_instance(&options.input)?;
    let result = parser::parse_instance(
        instance.problem(),
        instance.proof(),
        instance.rules(),
        options.parsing.into_config(),
    )?;
    Ok(result)
}

fn check_command(options: CheckCommandOptions) -> CliResult<carcara::Status> {
    let instance = get_instance(&options.input)?;
    let parser_config = options.parsing.into_config();
    let checker_config = (options.checking, options.tools).into_config();

    let collect_stats = options.stats.stats;
    if options.num_threads == 1 {
        check(
            instance.problem(),
            instance.proof(),
            instance.rules(),
            parser_config,
            checker_config,
            collect_stats,
        )
    } else {
        check_parallel(
            instance.problem(),
            instance.proof(),
            instance.rules(),
            parser_config,
            checker_config,
            collect_stats,
            options.num_threads as usize,
            options.stack.stack_size,
        )
    }
    .map_err(Into::into)
}

fn elaborate_command(
    options: ElaborateCommandOptions,
) -> CliResult<(
    carcara::Status,
    ast::Problem,
    ast::Proof,
    ast::pool::PrimitivePool,
)> {
    // A hole budget counts from here: parsing and checking the proof's other
    // steps come out of it, so the whole run stays within the budget.
    let started = std::time::Instant::now();
    let instance = get_instance(&options.input)?;

    // The RARE hole elaboration reuses the checking options' egglog settings.
    let hole_rewrite_options = carcara::RunEgglogOptions {
        continuous_saturation: options.checking.continuous_saturation,
        timeout: options
            .checking
            .rare_check_timeout
            .map(std::time::Duration::from_millis),
        print_egglog: options.checking.print_egglog,
        seed_from_goal: options.checking.rare_seed_from_goal,
        ..carcara::RunEgglogOptions::default()
    };
    let elaborate_hole_rewrites = options.elaboration.elaborate_hole_rewrites;
    let hole_threads = options.elaboration.hole_threads;
    let hole_isolate = options.elaboration.hole_isolate;
    let hole_memory_limit = options.elaboration.hole_memory_limit;
    let hole_rare_file = options.input.rare_file.clone().map(PathBuf::from);
    let hole_deadline = options
        .elaboration
        .hole_total_budget
        .map(|millis| started + std::time::Duration::from_millis(millis));
    let hole_check_only = options.elaboration.hole_check_only;
    let hole_batch = options.elaboration.hole_batch.unwrap_or(1);
    let hole_batch_timeout = options
        .elaboration
        .hole_batch_timeout
        .map(std::time::Duration::from_millis);
    let hole_batch_sequential = options.elaboration.hole_batch_sequential;
    let hole_batch_overlap = options.elaboration.hole_batch_by_overlap;
    let hole_batch_term_cap = options.elaboration.hole_batch_terms.unwrap_or(0);

    let checker_config = (options.checking, options.tools.clone()).into_config();
    let (elab_config, pipeline) = (options.elaboration, options.tools).into_config();
    let elab_config = elab_config
        .elaborate_hole_rewrites(elaborate_hole_rewrites)
        .hole_threads(hole_threads)
        .hole_isolate(hole_isolate)
        .hole_memory_limit_mb(hole_memory_limit)
        .hole_rare_file(hole_rare_file)
        .hole_deadline(hole_deadline)
        .hole_check_only(hole_check_only)
        .hole_batch(hole_batch)
        .hole_batch_timeout(hole_batch_timeout)
        .hole_batch_sequential(hole_batch_sequential)
        .hole_batch_overlap(hole_batch_overlap)
        .hole_batch_term_cap(hole_batch_term_cap)
        .hole_rewrite_options(hole_rewrite_options);

    check_and_elaborate(
        instance.problem(),
        instance.proof(),
        instance.rules(),
        options.parsing.into_config(),
        checker_config,
        elab_config,
        pipeline,
        options.stats.stats,
    )
    .map_err(CliError::CarcaraError)
}

fn bench_command(options: BenchCommandOptions) -> CliResult<()> {
    let instances = get_instances_from_paths(options.files.iter().map(|s| s.as_str()))?;
    if instances.is_empty() {
        log::warn!("no files passed");
        return Ok(());
    }

    log::info!(
        "running benchmark on {} files, doing {} runs each",
        instances.len(),
        options.num_runs
    );

    let checker_config = (options.checking, options.tools.clone()).into_config();
    let (elab_config, pipeline) = (options.elaboration, options.tools).into_config();

    if options.dump_to_csv {
        benchmarking::run_csv_benchmark(
            &instances,
            options.num_runs,
            options.num_jobs,
            options.parsing.into_config(),
            checker_config,
            options.elaborate.then_some((elab_config, pipeline)),
            "runs.csv",
            "steps.csv",
        )?;
        return Ok(());
    }

    let results: OnlineBenchmarkResults = benchmarking::run_benchmark(
        &instances,
        options.num_runs,
        options.num_jobs,
        options.parsing.into_config(),
        checker_config,
        options.elaborate.then_some((elab_config, pipeline)),
    );
    if results.is_empty() {
        println!("no benchmark data collected");
        return Ok(());
    }

    if results.had_error {
        println!("invalid");
    } else if results.is_holey {
        println!("holey");
    } else {
        println!("valid");
    }
    results.print(options.sort_by_total);
    Ok(())
}

fn slice_command(
    options: SliceCommandOptions,
    no_print_with_sharing: bool,
) -> CliResult<(ast::Problem, ast::Proof, ast::pool::PrimitivePool)> {
    let instance = get_instance(&options.input)?;
    let (problem, proof, _, mut pool) = parser::parse_instance(
        instance.problem(),
        instance.proof(),
        instance.rules(),
        options.parsing.into_config(),
    )?;

    let sliced = {
        let (sliced_proof, sliced_asserts) = slice::slice(
            &proof,
            &options.from,
            &mut pool,
            options.max_distance.unwrap_or(0),
        )
        .ok_or(CliError::InvalidSliceId(options.from.clone()))?;

        // Write sliced problem and proof to output paths, if provided
        if let Some(files) = options.sliced_output {
            let (proof_filename, problem_filename) = (&files[0], &files[1]);
            File::create(problem_filename)
                .and_then(|mut f| {
                    f.write_all(format!("{}", problem.prelude).as_bytes())?;
                    ast::printer::write_asserts(
                        &mut pool,
                        &problem.prelude,
                        &mut f,
                        &sliced_asserts,
                        false,
                    )?;
                    f.write_all(b"(check-sat)\n")?;
                    f.write_all(b"(exit)\n")
                })
                .map_err(|inner| carcara::Error::Io {
                    inner,
                    file: problem_filename.as_str().into(),
                })?;

            File::create(proof_filename)
                .and_then(|mut f| {
                    ast::printer::write_proof_to_dest(
                        &mut pool,
                        &problem.prelude,
                        &sliced_proof,
                        &mut f,
                        !no_print_with_sharing,
                    )?;
                    f.write_all(b"\n")
                })
                .map_err(|inner| carcara::Error::Io {
                    inner,
                    file: proof_filename.as_str().into(),
                })?;
        }

        sliced_proof
    };

    Ok((problem, sliced, pool))
}

fn generate_lia_problems_command(options: ParseCommandOptions, use_sharing: bool) -> CliResult<()> {
    use std::io::Write;

    let root_file_name = options.input.proof_file.clone();
    let instance = get_instance(&options.input)?;
    let instances = generate_lia_smt_instances(
        instance.problem(),
        instance.proof(),
        instance.rules(),
        options.parsing.into_config(),
        use_sharing,
    )?;
    for (id, content) in instances {
        let file_name = format!("{}-{}.lia_smt2", root_file_name, id);
        File::create(&file_name)
            .and_then(|mut f| write!(f, "{}", content))
            .map_err(|inner| carcara::Error::Io { inner, file: file_name.into() })?;
    }

    Ok(())
}

// Translation-related commands.
fn translate_command(options: TranslateCommandOptions) -> CliResult<()> {
    let instance = get_instance(&options.input)?;

    let (alethe_problem, mut alethe_proof, _, _) = parser::parse_instance(
        instance.problem(),
        instance.proof(),
        instance.rules(),
        options.parsing.into_config(),
    )?;

    // NOTE: currently supporting only translation into Eunoia.
    match &options.target {
        TranslationTarget::Eunoia => {
            translate_2_eunoia_command(&alethe_problem, &mut alethe_proof, &options.eunoia_mech)
        }
    }
}

fn translate_2_eunoia_command(
    alethe_problem: &ast::Problem,
    proof: &mut Proof,
    eunoia_mech: &str,
) -> CliResult<()> {
    let mut translator = translation::eunoia::alethe_2_eunoia::EunoiaTranslator::new(eunoia_mech);
    let eunoia_prelude = translator.translate_problem(alethe_problem);
    let eunoia_proof = translator.translate(proof);

    // Sink where to write the "prelude" of the problem and the path to the Eunoia mechanization.
    let mut buf_prelude = Vec::new();
    let s_exp_formatter_prelude =
        carcara::translation::eunoia::printer::SExpFormatter::new(&mut buf_prelude);
    let mut printer_prelude =
        carcara::translation::eunoia::printer::EunoiaPrinter::new(s_exp_formatter_prelude);

    printer_prelude.write_proof(&eunoia_prelude).unwrap();

    // Sink where to write the translated proof.
    let mut buf_proof = Vec::new();
    let s_exp_formatter_proof = translation::eunoia::printer::SExpFormatter::new(&mut buf_proof);
    let mut printer_proof = translation::eunoia::printer::EunoiaPrinter::new(s_exp_formatter_proof);

    printer_proof.write_proof(eunoia_proof).unwrap();

    println!("{}", std::str::from_utf8(&buf_prelude).unwrap());
    println!("{}", std::str::from_utf8(&buf_proof).unwrap());

    Ok(())
}

/// The child side of `--hole-isolate`: one hole in, its Alethe steps out.
fn reconstruct_hole_command(options: ReconstructHoleOptions) -> CliResult<()> {
    let mut input = String::new();
    io::stdin()
        .read_to_string(&mut input)
        .map_err(|e| carcara::Error::Io { inner: e, file: "<stdin>".into() })?;
    let rare_text =
        std::fs::read_to_string(&options.rare_file).map_err(|e| carcara::Error::Io {
            inner: e,
            file: options.rare_file.clone().into(),
        })?;
    let egglog_options = carcara::RunEgglogOptions {
        timeout: options
            .rare_check_timeout
            .map(std::time::Duration::from_millis),
        continuous_saturation: options.continuous_saturation,
        seed_from_goal: options.seed_from_goal,
        ..carcara::RunEgglogOptions::default()
    };
    let rules = parser::Source::new(std::path::Path::new(&options.rare_file), &rare_text);
    if options.batch {
        // Each verdict is printed and flushed as it is reached, so a parent
        // that kills this child still learns the verdicts before the kill.
        let mut report = |id: &str, verdict: &Result<(), String>| {
            let line = match verdict {
                Ok(()) => format!("hole {id} ok"),
                Err(reason) => format!("hole {id} failed: {}", reason.replace('\n', " | ")),
            };
            let mut out = io::stdout().lock();
            let _ = writeln!(out, "{line}");
            let _ = out.flush();
        };
        return match carcara::elaborator::rare_hole::check_batch_from_input(
            &input,
            rules,
            egglog_options,
            options.batch_sequential,
            &mut report,
        ) {
            Ok(_) => Ok(()),
            Err(error) => {
                eprintln!("{error}");
                std::process::exit(1);
            }
        };
    }
    match carcara::elaborator::rare_hole::reconstruct_from_input(
        &input,
        rules,
        egglog_options,
        options.check_only,
        // Reported as each phase completes and flushed at once, so the parent
        // learns how far a child got even when it kills it.
        &mut |name, elapsed| eprintln!("phase {name}={:.3}", elapsed.as_secs_f64()),
    ) {
        Ok(steps) => {
            let mut out = io::stdout().lock();
            for step in steps {
                writeln!(out, "{step}")
                    .map_err(|e| carcara::Error::Io { inner: e, file: "<stdout>".into() })?;
            }
            Ok(())
        }
        Err(error) => {
            eprintln!("{error}");
            std::process::exit(1);
        }
    }
}
