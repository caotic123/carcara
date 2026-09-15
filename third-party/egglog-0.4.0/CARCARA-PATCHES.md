# Vendored egglog 0.4.0

A copy of the `egglog` 0.4.0 crate from crates.io (`src/`, `build.rs`,
`Cargo.toml`, `LICENSE`, `README.md`, `CHANGELOG.md`; the crate's own tests
and benches are left out and the manifest's test/bench targets dropped), used
through `[patch.crates-io]` in the top-level `Cargo.toml`.

Changes against the released crate:

- `serialize-one-extractor.patch` (`src/serialize.rs`): `EGraph::serialize`
  built a fresh `Extractor` — a cost computation over the whole e-graph — for
  every primitive value it printed, so serializing an e-graph was quadratic
  in its size (about 2 ms per node on Carcara's hole e-graphs, 10 s for a
  5,500-node graph).  One extractor is now built lazily per `serialize`
  call.  Carcara's post-hoc reconstruction snapshots the e-graph through
  `serialize`, and this cost was where most holes died under a 30 s budget.
