use std::io::BufRead;
use std::rc::Rc;
use std::str::FromStr;

use crate::ast::{Constant, Operator};
use crate::{ast::rules::*, Error};

use crate::CarcaraResult;

use super::{Parser, ParserError, Reserved, Token};

#[derive(Debug, Clone)]
enum Body {
    Args(Vec<String>),
    Conclusion(Rc<RareTerm>),
    Blah(),
}

fn parse_rewrite_term<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rc<RareTerm>> {
    fn consume_head<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rc<RareTerm>> {
        let current = parser.next_token()?;
        match current {
            (Token::Bitvector { value, width }, _) => {
                return Ok(Rc::new(RareTerm::Const(Constant::BitVec(
                    value,
                    width.into(),
                ))))
            }
            (Token::Numeral(n), _) if parser.interpret_ints_as_reals() => {
                return Ok(Rc::new(RareTerm::Const(Constant::Real(n.into()))))
            }
            (Token::Numeral(n), _) => return Ok(Rc::new(RareTerm::Const(Constant::Integer(n)))),
            (Token::Decimal(r), _) => return Ok(Rc::new(RareTerm::Const(Constant::Real(r)))),
            (Token::String(s), _) => return Ok(Rc::new(RareTerm::Const(Constant::String(s)))),
            _ => {
                if let (symbol, _) = current {
                    if let Ok(op) = Operator::from_str(&symbol.to_string()) {
                        return Ok(Rc::new(RareTerm::Op(op)));
                    }

                    return Ok(Rc::new(RareTerm::Var(symbol.to_string())));
                }

                return Err(Error::Parser(
                    ParserError::UnexpectedToken(current.0),
                    current.1,
                ));
            }
        }
    }

    fn consume_continuation<'a, R: BufRead>(
        parser: &mut Parser<'a, R>,
    ) -> CarcaraResult<Rc<RareTerm>> {
        let current = &parser.current_token;
        return Ok(match current {
            Token::OpenParen => {
                let res: Rc<RareTerm> = parse_rewrite_term(parser)?;
                return Ok(res);
            }
            _ => consume_head(parser)?
        });
    }

    parser.expect_token(Token::OpenParen)?;
    let applicant = consume_head(parser)?;
    let mut args = parser.parse_sequence(consume_continuation, false)?;
    while true {
        let current = &parser.current_token;
        if let current = Token::OpenParen {
            args.push(parse_rewrite_term(parser)?);
        }
    }
    
    parser.expect_token(Token::CloseParen)?;
    return Ok(Rc::new(RareTerm::App(applicant, args)));
}

fn parse_parameters<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<RuleArg> {
    parser.expect_token(Token::OpenParen)?;
    match &parser.current_token {
        Token::Symbol(s) if s.starts_with("@") => {
            let arg_type = parser.expect_symbol()?;
            let arg_name = parser.expect_symbol()?;
            parser.expect_token(Token::CloseParen)?;
            Ok(RuleArg::TypeArg(
                arg_name,
                arg_type.strip_prefix("@").unwrap().to_string(),
            ))
        }
        _ => {
            let arg_name: String = parser.expect_symbol()?;
            let arg_type = parser.expect_symbol()?;
            match arg_type.strip_prefix("@") {
                Some(arg_type) => {
                    let arg_type = arg_type.to_string();
                    let current_token = &parser.current_token;
                    if let current_token = Token::Keyword("list".into()) {
                        let kind_of_arg = parser.expect_keyword()?;
                        parser.expect_token(Token::CloseParen)?;
                        if kind_of_arg != "list" {
                            return Err(Error::Parser(
                                ParserError::InvalidRareArgAttribute(kind_of_arg),
                                parser.current_position,
                            ));
                        }
                        return Ok(RuleArg::ListArg(arg_name, arg_type));
                    }
                    parser.expect_token(Token::CloseParen)?;
                    return Ok(RuleArg::UnitArg(arg_name, arg_type));
                }
                None => {
                    return Err(Error::Parser(
                        ParserError::InvalidRareArgFormat(arg_type),
                        parser.current_position,
                    ));
                }
            }
        }
    }
}

fn parse_args<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Vec<String>> {
    parser.expect_token(Token::OpenParen)?;
    return parser.parse_sequence(|parser| parser.expect_symbol(), false);
}

fn parse_body<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Body> {
    let qualified_arg: Vec<char> = parser.expect_keyword()?.chars().collect();
    match qualified_arg.as_slice() {
        ['a', 'r', 'g', 's', ..] => {
            return Ok(Body::Args(parse_args(parser)?));
        }
        ['c', 'o', 'n', 'c', 'l', 'u', 's', 'i', 'o', 'n', ..] => {
            let term = parse_rewrite_term(parser)?;
            parser.expect_token(Token::CloseParen)?;
            let rewrite_term = parse_rewrite_term(parser)?;
            print!("{:?}\n", rewrite_term);
            return Ok(Body::Conclusion(rewrite_term));
        }
        _ => {
            parser.expect_token(Token::OpenParen)?;
            print!("moto moto");
            return Ok(Body::Blah());
        }
    }
}

pub fn parse_rule<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<()> {
    parser.expect_token(Token::OpenParen)?;
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;
    parser.expect_token(Token::OpenParen)?;
    let args = parser.parse_sequence(parse_parameters, false)?;
    let body = parser.parse_sequence(parse_body, false)?;
    print!("{:?}", body);
    return Ok(());
}

pub fn parse_rare<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rules> {
    parse_rule(parser)?;

    return Ok(vec![]);
}
