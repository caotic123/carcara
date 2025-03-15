use std::cell::{Ref, RefCell, RefMut};
use std::io::BufRead;
use std::str::FromStr;

use indexmap::IndexMap;

use crate::ast::{Constant, Operator, Rc, Term};
use crate::{ast::rules::*, Error};

use crate::{match_rareterm, CarcaraResult};

use super::{Parser, ParserError, Reserved, Token};

#[derive(Debug, Clone)]
enum Body {
    Conclusion(Rc<RareTerm>),
    Premise(Vec<Rc<RareTerm>>),
}

// Parser a rare term until the closing outermost parenthesis, you may need to consume the outermost parenthesis after.
fn parse_rewrite_term<'a, R: BufRead, F>(
    parser: &mut Parser<'a, R>,
    holes: &mut Holes,
    stop_with: &[F],
) -> CarcaraResult<Rc<RareTerm>>
where
    F: Fn(Token) -> bool,
{
    fn consume_head<'a, R: BufRead>(
        parser: &mut Parser<'a, R>,
        holes: &mut Holes,
    ) -> CarcaraResult<Rc<RareTerm>> {
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
                if let (Token::Symbol(s), _) = current {
                    if let Ok(op) = Operator::from_str(&s) {
                        return Ok(Rc::new(RareTerm::Op(op)));
                    }

                    if let Some(hole) = holes.get(&s) {
                        return Ok(Rc::new(RareTerm::Hole(hole.clone())));
                    }

                    return Ok(Rc::new(RareTerm::Var(s)));
                }

                return Err(Error::Parser(
                    ParserError::UnexpectedToken(current.0),
                    current.1,
                ));
            }
        }
    }

    parser.expect_token(Token::OpenParen)?;
    let applicant = consume_head(parser, holes)?;
    let mut args = vec![];
    let mut current = parser.current_token.clone();
    loop {
        match current {
            Token::OpenParen => {
                args.push(parse_rewrite_term(parser, holes, stop_with)?);
                parser.expect_token(Token::CloseParen)?;
            }
            Token::CloseParen => break,
            token => {
                if Option::is_some(&stop_with.iter().find(|x| (**x)(token.clone()))) {
                    break;
                } else {
                    args.push(consume_head(parser, holes)?)
                }
            }
        }
        current = parser.current_token.clone();
    }

    return Ok(Rc::new(RareTerm::App(applicant, args)));
}

fn parse_parameters<'a, R: BufRead>(
    parser: &mut Parser<'a, R>,
    holes: &mut Holes,
) -> CarcaraResult<(String, TypeParameter)> {
    let term = parse_rewrite_term(
        parser,
        holes,
        vec![|x| {
            return if let Token::Keyword(_) = x {
                true
            } else {
                false
            };
        }]
        .as_slice(),
    )?;

    fn get_app_name(term: Rc<RareTerm>) -> String {
        if let RareTerm::App(func, _) = &*term {
            if let RareTerm::Var(name) = &**func {
                return name.clone();
            }
        }
        panic!("Malformed parameter")
    }

    let name = get_app_name(term.clone());

    if let Some(s) = match_rareterm!(Type(?v), term) {
        if s == "Type" {
            holes.insert(name.clone(), Rc::new(RefCell::new(None)));
        }
    }

    let current_token = &parser.current_token;
    match current_token {
        Token::CloseParen => {
            parser.expect_token(Token::CloseParen)?;
            return Ok((
                name,
                TypeParameter {
                    term,
                    attribute: AttributeParameters::None,
                },
            ));
        }
        Token::Keyword(_) => {
            let kind_of_arg = parser.expect_keyword()?;
            parser.expect_token(Token::CloseParen)?;
            if kind_of_arg == "list" {
                return Ok((
                    name,
                    TypeParameter {
                        term: term,
                        attribute: AttributeParameters::List,
                    },
                ));
            }
            return Err(Error::Parser(
                ParserError::InvalidRareArgAttribute(kind_of_arg),
                parser.current_position,
            ));
        }
        _ => Err(Error::Parser(
            ParserError::UnexpectedToken(current_token.clone()),
            parser.current_position,
        )),
    }
}

fn parse_args<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<(Vec<String>, Holes)> {
    fn parse_args<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Vec<String>> {
        parser.expect_token(Token::OpenParen)?;
        return parser.parse_sequence(|parser| parser.expect_symbol(), false);
    }

    let qualified_arg: Vec<char> = parser.expect_keyword()?.chars().collect();
    match qualified_arg.as_slice() {
        ['a', 'r', 'g', 's', ..] => {
            let mut holes = IndexMap::new();
            let args = parse_args(parser)?;
            for arg in &args {
                holes.insert(arg.clone(), Rc::new(RefCell::new(None)));
            }
            return Ok((args, holes));
        }
        attribute => {
            return Err(Error::Parser(
                ParserError::ExpectArgsFirst(attribute.iter().collect()),
                parser.current_position,
            ));
        }
    }
}

fn parse_body<'a, R: BufRead>(
    parser: &mut Parser<'a, R>,
    holes: &mut Holes,
) -> CarcaraResult<Body> {
    let qualified_arg: Vec<char> = parser.expect_keyword()?.chars().collect();
    match qualified_arg.as_slice() {
        ['c', 'o', 'n', 'c', 'l', 'u', 's', 'i', 'o', 'n', ..] => {
            let vec: Vec<fn(Token) -> bool> = vec![];
            let rewrite_term = parse_rewrite_term(parser, holes, vec.as_slice())?;
            return Ok(Body::Conclusion(rewrite_term));
        }
        ['p', 'r', 'e', 'm', 'i', 's', 'e', 's', ..] => {
            parser.expect_token(Token::OpenParen)?;
            let terms = parser.parse_sequence(
                |parser| {
                    let vec: Vec<fn(Token) -> bool> = vec![];
                    let term = parse_rewrite_term(parser, holes, vec.as_slice())?;
                    parser.expect_token(Token::CloseParen)?;
                    return Ok(term);
                },
                false,
            )?;
            return Ok(Body::Premise(terms));
        }
        attribute => {
            return Err(Error::Parser(
                ParserError::InvalidRareFunctionAttribute(attribute.iter().collect()),
                parser.current_position,
            ));
        }
    }
}

pub fn parse_rule<'a, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<RuleDefinition> {
    parser.expect_token(Token::OpenParen)?;
    parser.expect_token(Token::ReservedWord(Reserved::DeclareRareRule))?;
    let name = parser.expect_symbol()?;
    parser.expect_token(Token::OpenParen)?;
    let mut parameters_hole = IndexMap::new();
    let parameters = parser.parse_sequence(
        |parser| parse_parameters(parser, &mut parameters_hole),
        false,
    )?;
    pub struct BodyDefinition<'a> {
        args: (Vec<String>, Holes),
        premises: &'a Vec<Rc<RareTerm>>,
        conclusion: Option<Rc<RareTerm>>,
    }

    let mut body_definitions = BodyDefinition {
        args: parse_args(parser)?,
        premises: &vec![],
        conclusion: None,
    };

    let body = parser.parse_sequence(
        |parser| parse_body(parser, &mut body_definitions.args.1),
        false,
    )?;

    let body = body.iter().fold(body_definitions, |mut body, x| {
        match x {
            Body::Conclusion(term) => body.conclusion = Some((*term).clone()),
            Body::Premise(term) => body.premises = term,
        }
        return body;
    });

    if Option::is_none(&body.conclusion) {
        return Err(Error::Parser(
            ParserError::UndefinedRareConclusion(name),
            parser.current_position,
        ));
    }

    parser.expect_token(Token::CloseParen)?;
    return Ok(RuleDefinition {
        name,
        parameters: (
            parameters.iter().map(|x| x.clone()).collect(),
            parameters_hole,
        ),
        arguments: body.args.clone(),
        premises: body.premises.clone(),
        conclusion: body.conclusion.map(|x| x).unwrap(),
    });
}

pub fn parse_rare<'a, 'b, R: BufRead>(parser: &mut Parser<'a, R>) -> CarcaraResult<Rules>
where
    'a: 'b,
{
    let mut rules = vec![];
    let mut current = &parser.current_token;
    while *current != Token::Eof {
        rules.push(parse_rule(parser)?);
        current = &parser.current_token;
    }

    return Ok(rules
        .iter()
        .map(|x| (x.name.clone(), (*x).clone()))
        .collect());
}
