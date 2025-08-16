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

/// Parse: (declare-const <name> <sort-or-annotated> <attrs...>)
pub fn parse_declare_const<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<DeclConst> {
    pub fn parse_simple_annotated_sort<R: BufRead>(
        parser: &mut Parser<R>,
    ) -> CarcaraResult<ParsedAnnotatedSort> {
        // Expect "!"
        parser.expect_token(Token::ReservedWord(Reserved::Bang))?;

        // Parse the base sort after `!`
        let base_sort = parser.parse_sort(true)?;
        let mut var_name: Option<String> = None;
        let mut implicit = false;
        let mut requires: Vec<Vec<Rc<Term>>> = Vec::new();

        while parser.current_token != Token::CloseParen {
            let kw = parser.expect_keyword()?;
            match kw.as_str() {
                "var" => {
                    let name = parser.expect_symbol()?;
                    parser.insert_sorted_var((name.clone(), base_sort.clone()));
                    parser.state.sort_defs.insert(
                        name.clone(),
                        SortDef {
                            body: base_sort.clone(),
                            params: Vec::new(),
                        },
                    );
                    var_name = Some(name);
                }
                "implicit" => {
                    implicit = true;
                }
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

        Ok(ParsedAnnotatedSort {
            base_sort,
            var_name,
            implicit,
            requires,
        })
    }

    pub fn parser_sorted_param<R: BufRead>(
        parser: &mut Parser<R>,
    ) -> CarcaraResult<ParsedAnnotatedSort> {
        let current = &parser.current_token.clone();
        match current {
            Token::OpenParen => {
                parser.expect_token(Token::OpenParen)?;
                let current = &parser.current_token;
                if current == &Token::ReservedWord(Reserved::Bang) {
                    let annotated_sort = parse_simple_annotated_sort(parser)?;
                    parser.expect_token(Token::CloseParen)?;
                    return Ok(annotated_sort);
                }

                let sort = ParsedAnnotatedSort {
                    base_sort: parser.parse_sort(true)?,
                    var_name: None,
                    implicit: false,
                    requires: vec![],
                };

                parser.expect_token(Token::CloseParen)?;

                Ok(sort)
            }
            _ => Ok(ParsedAnnotatedSort {
                base_sort: parser.parse_sort(true)?,
                var_name: None,
                implicit: false,
                requires: vec![],
            }),
        }
    }

    pub fn parser_sort<R: BufRead>(
        parser: &mut Parser<R>,
    ) -> CarcaraResult<Vec<ParsedAnnotatedSort>> {
        let sorts;
        match &parser.current_token {
            Token::OpenParen => {
                parser.expect_token(Token::OpenParen)?;
                parser.expect_token(Token::Symbol("->".to_owned()))?;
                sorts = parser.parse_sequence(parser_sorted_param, true)?;
            }
            _ => {
                let sort = parser_sorted_param(parser)?;
                sorts = vec![sort];
            }
        }
        Ok(sorts)
    }

    parser.expect_token(Token::ReservedWord(Reserved::DeclareConst))?;
    let symbol = parser.expect_symbol()?;
    let sorts = parser_sort(parser)?;
    let attrs = parse_decl_attrs(parser)?;
    parser.expect_token(Token::CloseParen)?;
    let sorted : Vec<_> = sorts
        .iter()
        .map(|x| {
            if x.var_name.is_some() {
                parser
                    .pool
                    .add(Term::Sort(Sort::Var(x.var_name.clone().unwrap())))
            } else {
                x.base_sort.clone()
            }
        })
        .collect();

    let func_sort = parser.pool.add(Term::Sort(Sort::Function(sorted.clone())));
    parser.insert_sorted_var((symbol.clone(), func_sort.clone()));

    Ok(DeclConst {
        name: symbol,
        ty_params: sorts,
        sort: func_sort,
        attrs: attrs,
    })
}

fn parse_parameters<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<(String, TypeParameter)> {
    parser.expect_token(Token::OpenParen)?;
    let name = parser.expect_symbol()?;
    let term = parser.parse_sort(true)?;

    parser.insert_sorted_var((name.clone(), term.clone()));
    parser.state.sort_defs.insert(
        name.clone(),
        SortDef {
            body: term.clone(),
            params: Vec::default(),
        },
    );
    let current_token = &parser.current_token;
    match current_token {
        Token::CloseParen => {
            parser.expect_token(Token::CloseParen)?;
            Ok((
                name,
                TypeParameter {
                    term,
                    attribute: AttributeParameters::None,
                },
            ))
        }
        Token::Keyword(_) => {
            let kind_of_arg = parser.expect_keyword()?;
            parser.expect_token(Token::CloseParen)?;
            if kind_of_arg == "list" {
                return Ok((
                    name,
                    TypeParameter {
                        term,
                        attribute: AttributeParameters::List,
                    },
                ));
            }
            Err(Error::Parser(
                ParserError::InvalidRareArgAttribute(kind_of_arg),
                parser.current_position,
            ))
        }
        _ => Err(Error::Parser(
            ParserError::UnexpectedToken(current_token.clone()),
            parser.current_position,
        )),
    }
}

fn parse_body<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Body> {
    let qualified_arg: Vec<char> = parser.expect_keyword()?.chars().collect();
    match qualified_arg.as_slice() {
        ['c', 'o', 'n', 'c', 'l', 'u', 's', 'i', 'o', 'n', ..] => {
            let rewrite_term = parser.parse_term()?;
            Ok(Body::Conclusion(rewrite_term))
        }
        ['a', 'r', 'g', 's', ..] => {
            fn parse_args<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<Vec<String>> {
                parser.expect_token(Token::OpenParen)?;
                parser.parse_sequence(super::Parser::expect_symbol, false)
            }
            let args = parse_args(parser)?;
            Ok(Body::Args(args))
        }
        ['p', 'r', 'e', 'm', 'i', 's', 'e', 's', ..] => {
            parser.expect_token(Token::OpenParen)?;
            let terms = parser.parse_sequence(
                |parser| {
                    let term = parser.parse_term()?;
                    Ok(term)
                },
                false,
            )?;
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
    pub fn parse_pattern<R: BufRead>(
        parser: &mut Parser<R>,
    ) -> CarcaraResult<(Rc<Term>, Rc<Term>)> {
        parser.expect_token(Token::OpenParen)?;
        let lhs = parser.parse_term()?;
        let rhs = parser.parse_term()?;
        parser.expect_token(Token::CloseParen)?;
        Ok((lhs, rhs))
    }

    parser.expect_token(Token::ReservedWord(Reserved::Program))?;
    let name = parser.expect_symbol()?;
    parser.expect_token(Token::OpenParen)?;
    let parameters = parser.parse_sequence(|parser| parse_parameters(parser), false)?;
    parser.expect_token(Token::Keyword("signature".to_owned()))?;
    parser.expect_token(Token::OpenParen)?;
    let mut signature_params = parser.parse_sequence(|parser| parser.parse_sort(true), false)?;
    let signature_return = parser.parse_sort(true)?;
    signature_params.push(signature_return);
    let signature = parser
        .pool
        .add(Term::Sort(Sort::Function(signature_params.clone())));
    parser.insert_sorted_var((name.clone(), signature));

    parser.expect_token(Token::OpenParen)?;
    let patterns = parser.parse_sequence(
        |parser| {
            let pattern = parse_pattern(parser)?;
            Ok(pattern)
        },
        false,
    )?;

    parser.expect_token(Token::CloseParen)?;

    Ok(Program {
        name: name,
        parameters: parameters.into_iter().collect(),
        patterns: patterns,
        signature: signature_params,
    })
}

pub fn parse_rule<R: BufRead>(parser: &mut Parser<R>) -> CarcaraResult<RuleDefinition> {
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;
    parser.expect_token(Token::OpenParen)?;
    let parameters = parser.parse_sequence(|parser| parse_parameters(parser), false)?;

    let body_definitions = BodyDefinition {
        args: &vec![],
        premises: &vec![],
        conclusion: None,
    };

    let body = parser.parse_sequence(|parser| parse_body(parser), false)?;
    let body = body.iter().fold(body_definitions, |mut body, x| {
        match x {
            Body::Conclusion(term) => body.conclusion = Some((*term).clone()),
            Body::Premise(term) => body.premises = term,
            Body::Args(args) => body.args = args,
        }
        body
    });

    if Option::is_none(&body.conclusion) {
        return Err(Error::Parser(
            ParserError::UndefinedRareConclusion(name),
            parser.current_position,
        ));
    }

    return Ok(RuleDefinition {
        name,
        parameters: parameters.iter().cloned().collect(),
        arguments: body.args.clone(),
        premises: body.premises.clone(),
        conclusion: body.conclusion.unwrap(),
        is_elaborated: false,
    });
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
            _ => {
                return Err(Error::Parser(
                    ParserError::UnexpectedToken(current.clone()),
                    parser.current_position,
                ));
            }
        }

        current = &parser.current_token;
    }

    return Ok(RareStatements {
        rules: rules
            .iter()
            .map(|x| (x.name.clone(), (*x).clone()))
            .collect(),
        programs: programs
            .iter()
            .map(|x| (x.name.clone(), (*x).clone()))
            .collect(),
        consts: decls.into_iter().map(|x| (x.name.clone(), x)).collect(),
    });
}
