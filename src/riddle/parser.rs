use crate::riddle::lexer::{Lexer, Token};
use std::iter::Peekable;

pub enum Expr {
    Bool(bool),
    Int(i64),
    Real(i64, i64),
    QualifiedId { ids: Vec<String> },
    Sum { terms: Vec<Expr> },
    Sub { terms: Vec<Expr> },
    Mul { factors: Vec<Expr> },
    Div { left: Box<Expr>, right: Box<Expr> },
    Function { name: Vec<String>, args: Vec<Expr> },
    Eq { left: Box<Expr>, right: Box<Expr> },
    Neq { left: Box<Expr>, right: Box<Expr> },
    Lt { left: Box<Expr>, right: Box<Expr> },
    Leq { left: Box<Expr>, right: Box<Expr> },
    Gt { left: Box<Expr>, right: Box<Expr> },
    Geq { left: Box<Expr>, right: Box<Expr> },
    Or { terms: Vec<Expr> },
    And { terms: Vec<Expr> },
}

pub struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Parser {
            lexer: lexer.peekable(),
        }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.lexer.peek()
    }

    fn next(&mut self) -> Option<Token> {
        self.lexer.next()
    }

    fn expect(&mut self, expected: Token) -> Result<Token, String> {
        match self.next() {
            Some(token) if token == expected => Ok(token),
            Some(token) => Err(format!("Expected {:?}, found {:?}", expected, token)),
            None => Err(format!("Expected {:?}, found end of input", expected)),
        }
    }

    pub fn parse_expression(&mut self) -> Result<Expr, String> {
        self.parse_or_expression()
    }

    fn parse_or_expression(&mut self) -> Result<Expr, String> {
        let mut terms = vec![self.parse_and_expression()?];
        while let Some(Token::Bar) = self.peek() {
            self.next(); // consume '|'
            terms.push(self.parse_and_expression()?);
        }
        if terms.len() == 1 {
            Ok(terms.remove(0))
        } else {
            Ok(Expr::Or { terms })
        }
    }

    fn parse_and_expression(&mut self) -> Result<Expr, String> {
        let mut terms = vec![self.parse_equality_expression()?];
        while let Some(Token::Amp) = self.peek() {
            self.next(); // consume '&'
            terms.push(self.parse_equality_expression()?);
        }
        if terms.len() == 1 {
            Ok(terms.remove(0))
        } else {
            Ok(Expr::And { terms })
        }
    }

    fn parse_equality_expression(&mut self) -> Result<Expr, String> {
        let left = self.parse_relational_expression()?;
        match self.peek() {
            Some(Token::Equal) => {
                self.next(); // consume '='
                let right = self.parse_relational_expression()?;
                Ok(Expr::Eq {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            Some(Token::NotEqual) => {
                self.next(); // consume '!='
                let right = self.parse_relational_expression()?;
                Ok(Expr::Neq {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            _ => Ok(left),
        }
    }

    fn parse_relational_expression(&mut self) -> Result<Expr, String> {
        let left = self.parse_additive_expression()?;
        match self.peek() {
            Some(Token::LessThan) => {
                self.next(); // consume '<'
                let right = self.parse_additive_expression()?;
                Ok(Expr::Lt {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            Some(Token::LessEqual) => {
                self.next(); // consume '<='
                let right = self.parse_additive_expression()?;
                Ok(Expr::Leq {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            Some(Token::GreaterThan) => {
                self.next(); // consume '>'
                let right = self.parse_additive_expression()?;
                Ok(Expr::Gt {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            Some(Token::GreaterEqual) => {
                self.next(); // consume '>='
                let right = self.parse_additive_expression()?;
                Ok(Expr::Geq {
                    left: Box::new(left),
                    right: Box::new(right),
                })
            }
            _ => Ok(left),
        }
    }

    fn parse_additive_expression(&mut self) -> Result<Expr, String> {
        let mut terms = vec![self.parse_multiplicative_expression()?];
        while let Some(token) = self.peek() {
            match token {
                Token::Plus => {
                    self.next(); // consume '+'
                    terms.push(self.parse_multiplicative_expression()?);
                }
                Token::Minus => {
                    self.next(); // consume '-'
                    let right = self.parse_multiplicative_expression()?;
                    terms.push(Expr::Sub { terms: vec![right] });
                }
                _ => break,
            }
        }
        if terms.len() == 1 {
            Ok(terms.remove(0))
        } else {
            Ok(Expr::Sum { terms })
        }
    }

    fn parse_multiplicative_expression(&mut self) -> Result<Expr, String> {
        let mut factors = vec![self.parse_primary_expression()?];
        while let Some(token) = self.peek() {
            match token {
                Token::Asterisk => {
                    self.next(); // consume '*'
                    factors.push(self.parse_primary_expression()?);
                }
                Token::Slash => {
                    self.next(); // consume '/'
                    let right = self.parse_primary_expression()?;
                    let left = factors.pop().unwrap();
                    return Ok(Expr::Div {
                        left: Box::new(left),
                        right: Box::new(right),
                    });
                }
                _ => break,
            }
        }
        if factors.len() == 1 {
            Ok(factors.remove(0))
        } else {
            Ok(Expr::Mul { factors })
        }
    }

    fn parse_primary_expression(&mut self) -> Result<Expr, String> {
        match self.next() {
            Some(Token::BoolLiteral(value)) => Ok(Expr::Bool(value)),
            Some(Token::IntLiteral(value)) => Ok(Expr::Int(value)),
            Some(Token::RealLiteral(int_part, frac_part)) => Ok(Expr::Real(int_part, frac_part)),
            Some(Token::Identifier(name)) => {
                let mut ids = vec![name];
                while let Some(Token::Dot) = self.peek() {
                    self.next(); // consume '.'
                    if let Some(Token::Identifier(next_name)) = self.next() {
                        ids.push(next_name);
                    } else {
                        return Err("Expected identifier after '.'".to_string());
                    }
                }
                Ok(Expr::QualifiedId { ids })
            }
            Some(Token::LParen) => {
                let expr = self.parse_expression()?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            Some(token) => Err(format!("Unexpected token: {:?}", token)),
            None => Err("Unexpected end of input".to_string()),
        }
    }
}
