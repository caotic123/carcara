// parser/rare.rs

use super::{Parser, ParserError, Reserved, SortDef, Token};
use crate::ast::*;
use crate::CarcaraResult;
use crate::{ast::rare_rules::*, Error};
use indexmap::IndexMap;
use std::io::BufRead;

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<Term>),
    Premise(Vec<Rc<Term>>),
    Args(Vec<String>),
}

fn parse_parameters<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<(String, TypeParameter)> {
    parser.expect_token(Token::OpenParen)?;
    let name = parser.expect_symbol()?;
    let base_sort = parser.parse_sort(true)?;

    match &parser.current_token {
        Token::CloseParen => {
            parser.expect_token(Token::CloseParen)?;
            parser.insert_sorted_var((name.clone(), base_sort.clone()));
            parser.state.sort_defs.insert(
                name.clone(),
                SortDef {
                    body: base_sort.clone(),
                    params: Vec::default(),
                },
            );
            Ok((
                name,
                TypeParameter {
                    term: base_sort,
                    attribute: AttributeParameters::None,
                },
            ))
        }
        Token::Keyword(_) => {
            let kind_of_arg = parser.expect_keyword()?;
            parser.expect_token(Token::CloseParen)?;
            if kind_of_arg == "list" {
                let list_sort = parser
                    .pool
                    .add(Term::Sort(Sort::RareList(base_sort.clone())));
                // Keep the local variable bound to element sort so list args can
                // still appear where a single element is expected.
                parser.insert_sorted_var((name.clone(), base_sort.clone()));
                parser.state.sort_defs.insert(
                    name.clone(),
                    SortDef {
                        body: base_sort,
                        params: Vec::default(),
                    },
                );
                return Ok((
                    name,
                    TypeParameter {
                        term: list_sort,
                        attribute: AttributeParameters::List,
                    },
                ));
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
    let attribute = parser.expect_keyword()?;
    match attribute.as_str() {
        "conclusion" => Ok(Body::Conclusion(parser.parse_term()?)),
        "args" => {
            parser.expect_token(Token::OpenParen)?;
            let args = parser.parse_sequence(super::Parser::expect_symbol, false)?;
            Ok(Body::Args(args))
        }
        "premises" => {
            parser.expect_token(Token::OpenParen)?;
            let terms = parser.parse_sequence(super::Parser::parse_term, false)?;
            Ok(Body::Premise(terms))
        }
        _ => Err(Error::Parser(
            ParserError::InvalidRareFunctionAttribute(attribute),
            parser.current_position,
        )),
    }
}

#[derive(Default)]
struct BodyDefinition {
    args: Vec<String>,
    premises: Vec<Rc<Term>>,
    conclusion: Option<Rc<Term>>,
}

pub fn parse_rule<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<RuleDefinition> {
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;

    // local scope for rule parameters, premises bindings, etc.
    parser.state.symbol_table.push_scope();
    let result = (|| {
        parser.expect_token(Token::OpenParen)?;
        let parameters = parser.parse_sequence(|p| parse_parameters(p), false)?;

        let mut body = BodyDefinition::default();
        for item in parser.parse_sequence(parse_body, false)? {
            match item {
                Body::Conclusion(term) => body.conclusion = Some(term),
                Body::Premise(premises) => body.premises = premises,
                Body::Args(args) => body.args = args,
            }
        }

        let conclusion = body.conclusion.ok_or_else(|| {
            Error::Parser(
                ParserError::UndefinedRareConclusion(name.clone()),
                parser.current_position,
            )
        })?;
        if !matches!(
            conclusion.as_ref(),
            Term::Op(Operator::Equals, args) if args.len() == 2
        ) {
            return Err(Error::Parser(
                ParserError::InvalidRareConclusion(name.clone()),
                parser.current_position,
            ));
        }
        if body.premises.iter().any(|premise| {
            !matches!(
                premise.as_ref(),
                Term::Op(Operator::Equals | Operator::Distinct, args) if args.len() == 2
            )
        }) {
            return Err(Error::Parser(
                ParserError::InvalidRarePremise(name.clone()),
                parser.current_position,
            ));
        }

        let parameters: IndexMap<_, _> = parameters.into_iter().collect();
        if let Some(argument) = body
            .args
            .iter()
            .find(|argument| !parameters.contains_key(*argument))
        {
            return Err(Error::Parser(
                ParserError::UndeclaredRareArgument(name.clone(), argument.clone()),
                parser.current_position,
            ));
        }

        Ok(RuleDefinition {
            name,
            parameters,
            arguments: body.args,
            premises: body.premises,
            conclusion,
            is_elaborated: false,
        })
    })();
    parser.state.symbol_table.pop_scope();
    result
}

pub fn parse_rare<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Rules> {
    let mut rules = vec![];
    let mut current = &parser.current_token;

    while *current != Token::Eof {
        parser.expect_token(Token::OpenParen)?;
        current = &parser.current_token;
        match current {
            Token::ReservedWord(Reserved::DeclareRareRule) => rules.push(parse_rule(parser)?),
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
        rules: rules.into_iter().map(|x| (x.name.clone(), x)).collect(),
    })
}
