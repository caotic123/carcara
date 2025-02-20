use std::io::BufRead;
use std::ops::Index;

use crate::{ast::rules::*, Error};

use crate::CarcaraResult;

use super::{Parser, ParserError, Reserved, Token};

#[derive(Debug, Clone)]
enum RuleArg {
    TypeArg(String, String),
    UnitArg(String, String),
    ListArg(String, String),
}

fn parse_arg<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<RuleArg> {
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

pub fn parse_rule<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<()> {
    parser.expect_token(Token::OpenParen)?;
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;
    parser.expect_token(Token::OpenParen)?;
    let args = parser.parse_sequence(parse_arg, false)?;
    println!("{:?}", args);
    return Ok(());
}

pub fn parse_rare<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rules> {
    parse_rule(parser)?;

    return Ok(vec![]);
}
