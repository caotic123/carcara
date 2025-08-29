// parser/rare.rs

use super::{Parser, ParserError, Reserved, SortDef, Token};
use crate::ast::*;
use crate::CarcaraResult;
use crate::{ast::rare_rules::*, Error};
use std::io::BufRead;

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<Term>),
    Premise(Vec<Rc<Term>>),
    Args(Vec<String>),
}

fn parse_maybe_qualified_symbol<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<String> {
    let mut symbol = parser.expect_symbol()?;
    if let Token::Keyword(_) = &parser.current_token {
        parser.expect_keyword()?;
        let s = parser.expect_keyword()?;
        symbol = format!("{}::{}", symbol, s);
    }
    Ok(symbol)
}


fn parse_simple_annotated_sort_after_bang<R: BufRead>(
    parser: &mut Parser<R>,
) -> CarcaraResult<ParsedAnnotatedSort> {

    parser.expect_token(Token::ReservedWord(Reserved::Bang))?;
    let base_sort = parser.parse_sort(true)?;
    let mut var_name: Option<String> = None;
    let mut implicit = false;
    let mut requires: Vec<Vec<Rc<Term>>> = Vec::new();

    while parser.current_token != Token::CloseParen {
        let kw = parser.expect_keyword()?;
        match kw.as_str() {
            "var" => {
                let name = parser.expect_symbol()?;
                // local param name available while parsing this definition
                parser.insert_sorted_var((name.clone(), base_sort.clone()));
                // also allow it to appear as a sort variable
                parser.state.sort_defs.insert(
                    name.clone(),
                    SortDef { body: base_sort.clone(), params: Vec::new() },
                );
                var_name = Some(name);
            }
            "implicit" => implicit = true,
            "requires" => {
                parser.expect_token(Token::OpenParen)?;
                let terms = parser.parse_sequence(|p| p.parse_term(), false)?;
                parser.expect_token(Token::CloseParen)?;
                requires.push(terms);
            }
            other => {
                return Err(Error::Parser(
                    ParserError::InvalidRareArgAttribute(other.to_string()),
                    parser.current_position,
                ));
            }
        }
    }

    Ok(ParsedAnnotatedSort { base_sort, var_name, implicit, requires })
}

fn parse_sorted_param_slot<R: BufRead>(
    parser: &mut Parser<R>,
) -> CarcaraResult<ParsedAnnotatedSort> {
    let current = parser.current_token.clone();
    match current {
        Token::OpenParen => {
            parser.expect_token(Token::OpenParen)?;
            if parser.current_token == Token::ReservedWord(Reserved::Bang) {
                let annotated = parse_simple_annotated_sort_after_bang(parser)?;
                parser.expect_token(Token::CloseParen)?;
                Ok(annotated)
            } else {
                let sort = ParsedAnnotatedSort {
                    base_sort: parser.parser_app_sorted(true)?,
                    var_name: None,
                    implicit: false,
                    requires: vec![],
                };
                Ok(sort)
            }
        }
        _ => Ok(ParsedAnnotatedSort {
            base_sort: parser.parse_sort(true)?,
            var_name: None,
            implicit: false,
            requires: vec![],
        }),
    }
}

fn parse_arrow_or_sort<R: BufRead>(
    parser: &mut Parser<R>,
) -> CarcaraResult<Vec<ParsedAnnotatedSort>> {
    match &parser.current_token {
        Token::OpenParen => {
            parser.expect_token(Token::OpenParen)?;
            parser.expect_token(Token::Symbol("->".to_owned()))?;
            let v = parser.parse_sequence(parse_sorted_param_slot, true)?;
            Ok(v)
        }
        _ => Ok(vec![parse_sorted_param_slot(parser)?]),
    }
}

fn build_function_sort_from_slots<R: BufRead>(
    parser: &mut Parser<R>,
    slots: &[ParsedAnnotatedSort],
) -> Rc<Term> {
    let terms: Vec<_> = slots
        .iter()
        .filter(|s| !s.implicit)
        .map(|s| {
            if let Some(v) = &s.var_name {
                parser.pool.add(Term::Sort(Sort::Var(v.clone())))
            } else {
                s.base_sort.clone()
            }
        })
        .collect();
    parser.pool.add(Term::Sort(Sort::Function(terms)))
}

fn parse_typed_param_entry<R: BufRead>(
    parser: &mut Parser<R>,
) -> CarcaraResult<ParsedAnnotatedSort> {

    parser.expect_token(Token::OpenParen)?;
    let name = parser.expect_symbol()?;
    let base_sort = parser.parse_sort(true)?;

    // local param for this definition
    parser.insert_sorted_var((name.clone(), base_sort.clone()));
    parser.state.sort_defs.insert(
        name.clone(),
        SortDef { body: base_sort.clone(), params: Vec::new() },
    );

    let mut implicit = false;
    let mut requires: Vec<Vec<Rc<Term>>> = Vec::new();

    while parser.current_token != Token::CloseParen {
        let kw = parser.expect_keyword()?;
        match kw.as_str() {
            "implicit" => implicit = true,
            "requires" => {
                parser.expect_token(Token::OpenParen)?;
                let terms = parser.parse_sequence(|pp| pp.parse_term(), false)?;
                parser.expect_token(Token::CloseParen)?;
                requires.push(terms);
            }
            other => {
                return Err(Error::Parser(
                    ParserError::InvalidRareArgAttribute(other.to_string()),
                    parser.current_position,
                ));
            }
        }
    }
    parser.expect_token(Token::CloseParen)?;

    Ok(ParsedAnnotatedSort { base_sort, var_name: Some(name), implicit, requires })
}

fn parse_decl_attrs<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Vec<DeclAttr>> {
    let mut attrs = Vec::new();
    while parser.current_token != Token::CloseParen {
        let kw = parser.expect_keyword()?;
        match kw.as_str() {
            "left-assoc" => attrs.push(DeclAttr::LeftAssoc),
            "right-assoc" => attrs.push(DeclAttr::RightAssoc),
            "right-assoc-nil" => {
                let t = parser.parse_term()?;
                attrs.push(DeclAttr::RightAssocNil(t));
            }
            "chainable" => {
                let reducer = parser.expect_symbol()?;
                attrs.push(DeclAttr::Chainable(reducer));
            }
            "binder" => {
                let binder = parser.expect_symbol()?;
                attrs.push(DeclAttr::Binder(binder));
            }
            "pairwise" => {
                let binder = parser.expect_symbol()?;
                attrs.push(DeclAttr::Pairwise(binder));
            }
            other => {
                return Err(Error::Parser(
                    ParserError::InvalidRareArgAttribute(other.to_owned()),
                    parser.current_position,
                ));
            }
        }
    }
    Ok(attrs)
}

// ======================= Declarations =======================

pub fn parse_declare_parameterized_const<R: BufRead>(
    parser: &mut Parser<R>,
) -> CarcaraResult<DeclConst> {
    parser.expect_token(Token::ReservedWord(Reserved::DeclareParameterizedConst))?;
    let symbol = parse_maybe_qualified_symbol(parser)?;

    // local scope for params & annotated names
    parser.state.symbol_table.push_scope();

    // do all parsing under the local scope
    parser.expect_token(Token::OpenParen)?;
    let params: Vec<ParsedAnnotatedSort> = parser.parse_sequence(parse_typed_param_entry, false)?;
    let slots = parse_arrow_or_sort(parser)?;
    let attrs = parse_decl_attrs(parser)?;
    parser.expect_token(Token::CloseParen)?;

    // compute function sort while still having local names alive
    let mut all_slots = slots;
    all_slots.extend_from_slice(params.as_slice());
    let func_sort = build_function_sort_from_slots(parser, &all_slots);

    parser.state.symbol_table.pop_scope();

    // register the CONST *globally* (after pop)
    parser.insert_sorted_var((symbol.clone(), func_sort.clone()));

    Ok(DeclConst {
        name: symbol,
        parametrized_params: params,
        ty_params: all_slots,
        sort: func_sort,
        attrs,
        is_parameterized: true,
    })
}

pub fn parse_declare_const<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<DeclConst> {
    parser.expect_token(Token::ReservedWord(Reserved::DeclareConst))?;
    let symbol = parse_maybe_qualified_symbol(parser)?;

    // local scope for any annotated variables in the sort
    parser.state.symbol_table.push_scope();

    let slots = parse_arrow_or_sort(parser)?;
    let attrs = parse_decl_attrs(parser)?;
    parser.expect_token(Token::CloseParen)?;

    let func_sort = build_function_sort_from_slots(parser, &slots);

    parser.state.symbol_table.pop_scope();

    // register globally
    parser.insert_sorted_var((symbol.clone(), func_sort.clone()));

    Ok(DeclConst {
        name: symbol,
        parametrized_params: vec![],
        ty_params: slots,
        sort: func_sort,
        attrs,
        is_parameterized: false,
    })
}

// ======================= Rules & Programs =======================

fn parse_parameters<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<(String, TypeParameter)> {
    parser.expect_token(Token::OpenParen)?;
    let name = parser.expect_symbol()?;
    let term = parser.parse_sort(true)?;

    // local binding of param name with its sort
    parser.insert_sorted_var((name.clone(), term.clone()));
    // and as sort alias for use in sorts
    parser.state.sort_defs.insert(
        name.clone(),
        SortDef { body: term.clone(), params: Vec::default() },
    );

    match &parser.current_token {
        Token::CloseParen => {
            parser.expect_token(Token::CloseParen)?;
            Ok((name, TypeParameter { term, attribute: AttributeParameters::None }))
        }
        Token::Keyword(_) => {
            let kind_of_arg = parser.expect_keyword()?;
            parser.expect_token(Token::CloseParen)?;
            if kind_of_arg == "list" {
                return Ok((name, TypeParameter { term, attribute: AttributeParameters::List }));
            }
            Err(Error::Parser(
                ParserError::InvalidRareArgAttribute(kind_of_arg),
                parser.current_position,
            ))
        }
        other => Err(Error::Parser(
            ParserError::UnexpectedToken(other.clone()),
            parser.current_position,
        )),
    }
}

fn parse_body<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Body> {
    let qualified_arg: Vec<char> = parser.expect_keyword()?.chars().collect();
    match qualified_arg.as_slice() {
        ['c','o','n','c','l','u','s','i','o','n', ..] => {
            let rewrite_term = parser.parse_term()?;
            Ok(Body::Conclusion(rewrite_term))
        }
        ['a','r','g','s', ..] => {
            parser.expect_token(Token::OpenParen)?;
            let args = parser.parse_sequence(super::Parser::expect_symbol, false)?;
            Ok(Body::Args(args))
        }
        ['p','r','e','m','i','s','e','s', ..] => {
            parser.expect_token(Token::OpenParen)?;
            let terms = parser.parse_sequence(|p| p.parse_term(), false)?;
            Ok(Body::Premise(terms))
        }
        attribute => Err(Error::Parser(
            ParserError::InvalidRareFunctionAttribute(attribute.iter().collect()),
            parser.current_position,
        )),
    }
}

struct BodyDefinition<'a> {
    args: &'a Vec<String>,
    premises: &'a Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

pub fn parse_program<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Program> {
    fn parse_pattern<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<(Rc<Term>, Rc<Term>)> {
        parser.expect_token(Token::OpenParen)?;
        let lhs = parser.parse_term()?;
        let rhs = parser.parse_term()?;
        parser.expect_token(Token::CloseParen)?;
        Ok((lhs, rhs))
    }

    parser.expect_token(Token::ReservedWord(Reserved::Program))?;
    let name = parse_maybe_qualified_symbol(parser)?;

    // local scope for params/signature variables/patterns
    parser.state.symbol_table.push_scope();

    parser.expect_token(Token::OpenParen)?;
    let parameters = parser.parse_sequence(|p| parse_parameters(p), false)?;

    // :signature (T ...) ...
    parser.expect_token(Token::Keyword("signature".to_owned()))?;
    parser.expect_token(Token::OpenParen)?;
    let mut signature_params = parser.parse_sequence(|p| p.parse_sort(true), false)?;
    let signature_return = parser.parse_sort(true)?;
    signature_params.push(signature_return);
    let signature_term = parser
        .pool
        .add(Term::Sort(Sort::Function(signature_params.clone())));

    parser.insert_sorted_var((name.clone(), signature_term.clone()));

    parser.expect_token(Token::OpenParen)?;
    let patterns = parser.parse_sequence(|p| parse_pattern(p), false)?;
    parser.expect_token(Token::CloseParen)?;

    parser.state.symbol_table.pop_scope();
    parser.insert_sorted_var((name.clone(), signature_term));

    Ok(Program {
        name,
        parameters: parameters.into_iter().collect(),
        patterns,
        signature: signature_params,
    })
}

pub fn parse_rule<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<RuleDefinition> {
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;

    // local scope for rule parameters, premises bindings, etc.
    parser.state.symbol_table.push_scope();

    parser.expect_token(Token::OpenParen)?;
    let parameters = parser.parse_sequence(|p| parse_parameters(p), false)?;

    let body_definitions = BodyDefinition { args: &vec![], premises: &vec![], conclusion: None };
    let body = parser.parse_sequence(|p| parse_body(p), false)?;
    let body = body.iter().fold(body_definitions, |mut body, x| {
        match x {
            Body::Conclusion(term) => body.conclusion = Some((*term).clone()),
            Body::Premise(term) => body.premises = term,
            Body::Args(args) => body.args = args,
        }
        body
    });

    if body.conclusion.is_none() {
        // pop before error so we don't leave scopes dangling
        parser.state.symbol_table.pop_scope();
        return Err(Error::Parser(
            ParserError::UndefinedRareConclusion(name),
            parser.current_position,
        ));
    }


    parser.state.symbol_table.pop_scope();

    Ok(RuleDefinition {
        name,
        parameters: parameters.iter().cloned().collect(),
        arguments: body.args.clone(),
        premises: body.premises.clone(),
        conclusion: body.conclusion.unwrap(),
        is_elaborated: false,
    })
}

pub fn parse_rare<'a, 'b, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rules>
where
    'a: 'b,
{
    let mut rules = vec![];
    let mut programs = vec![];
    let mut decls = vec![];
    let mut current = &parser.current_token;

    while *current != Token::Eof {
        parser.expect_token(Token::OpenParen)?;
        current = &parser.current_token;
        match current {
            Token::ReservedWord(Reserved::DeclareRareRule) => rules.push(parse_rule(parser)?),
            Token::ReservedWord(Reserved::Program) => programs.push(parse_program(parser)?),
            Token::ReservedWord(Reserved::DeclareConst) => decls.push(parse_declare_const(parser)?),
            Token::ReservedWord(Reserved::DeclareParameterizedConst) => {
                decls.push(parse_declare_parameterized_const(parser)?)
            }
            _ => {
                return Err(Error::Parser(
                    ParserError::UnexpectedToken(current.clone()),
                    parser.current_position,
                ));
            }
        }
        current = &parser.current_token;
    }

    Ok(RareStatements {
        rules: rules.iter().map(|x| (x.name.clone(), (*x).clone())).collect(),
        programs: programs.iter().map(|x| (x.name.clone(), (*x).clone())).collect(),
        consts: decls.into_iter().map(|x| (x.name.clone(), x)).collect(),
    })
}
