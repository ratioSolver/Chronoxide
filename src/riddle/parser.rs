use crate::riddle::lexer::{Lexer, Token};
use std::iter::Peekable;

#[derive(Debug, PartialEq)]
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

#[derive(Debug, PartialEq)]
pub enum Statement {
    Expr(Expr),
    LocalField { field_type: Vec<String>, fields: Vec<(String, Option<Expr>)> },
    Assign { name: Vec<String>, value: Expr },
    ForAll { var_type: Vec<String>, var_name: String, statements: Vec<Statement> },
    Disjunction { disjuncts: Vec<(Vec<Statement>, Expr)> },
    Return { value: Expr },
}

pub(super) struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Parser { lexer: lexer.peekable() }
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
        if terms.len() == 1 { Ok(terms.remove(0)) } else { Ok(Expr::Or { terms }) }
    }

    fn parse_and_expression(&mut self) -> Result<Expr, String> {
        let mut terms = vec![self.parse_equality_expression()?];
        while let Some(Token::Amp) = self.peek() {
            self.next(); // consume '&'
            terms.push(self.parse_equality_expression()?);
        }
        if terms.len() == 1 { Ok(terms.remove(0)) } else { Ok(Expr::And { terms }) }
    }

    fn parse_equality_expression(&mut self) -> Result<Expr, String> {
        let left = self.parse_relational_expression()?;
        match self.peek() {
            Some(Token::Equal) => {
                self.next(); // consume '='
                let right = self.parse_relational_expression()?;
                Ok(Expr::Eq { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::NotEqual) => {
                self.next(); // consume '!='
                let right = self.parse_relational_expression()?;
                Ok(Expr::Neq { left: Box::new(left), right: Box::new(right) })
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
                Ok(Expr::Lt { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::LessEqual) => {
                self.next(); // consume '<='
                let right = self.parse_additive_expression()?;
                Ok(Expr::Leq { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::GreaterThan) => {
                self.next(); // consume '>'
                let right = self.parse_additive_expression()?;
                Ok(Expr::Gt { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::GreaterEqual) => {
                self.next(); // consume '>='
                let right = self.parse_additive_expression()?;
                Ok(Expr::Geq { left: Box::new(left), right: Box::new(right) })
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
        if terms.len() == 1 { Ok(terms.remove(0)) } else { Ok(Expr::Sum { terms }) }
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
                    return Ok(Expr::Div { left: Box::new(left), right: Box::new(right) });
                }
                _ => break,
            }
        }
        if factors.len() == 1 { Ok(factors.remove(0)) } else { Ok(Expr::Mul { factors }) }
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
                if let Some(Token::LParen) = self.peek() {
                    self.next(); // consume '('
                    let mut args = Vec::new();
                    if let Some(Token::RParen) = self.peek() {
                        self.next(); // consume ')'
                    } else {
                        loop {
                            args.push(self.parse_expression()?);
                            if let Some(Token::Comma) = self.peek() {
                                self.next(); // consume ','
                            } else {
                                break;
                            }
                        }
                        self.expect(Token::RParen)?;
                    }
                    Ok(Expr::Function { name: ids, args })
                } else {
                    Ok(Expr::QualifiedId { ids })
                }
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

    pub fn parse_statement(&mut self) -> Result<Statement, String> {
        match self.peek() {
            Some(Token::Bool | Token::Int | Token::Real | Token::String) => {
                let field_type = match self.next().unwrap() {
                    Token::Bool => vec!["bool".to_string()],
                    Token::Int => vec!["int".to_string()],
                    Token::Real => vec!["real".to_string()],
                    _ => unreachable!(),
                };
                let mut fields = Vec::new();
                loop {
                    if let Some(Token::Identifier(name)) = self.next() {
                        let init_expr = if let Some(Token::Equal) = self.peek() {
                            self.next(); // consume '='
                            Some(self.parse_expression()?)
                        } else {
                            None
                        };
                        fields.push((name, init_expr));
                    } else {
                        return Err("Expected identifier in field declaration".to_string());
                    }
                    if let Some(Token::Comma) = self.peek() {
                        self.next(); // consume ','
                    } else {
                        break;
                    }
                }
                Ok(Statement::LocalField { field_type, fields })
            }
            Some(Token::Identifier(id)) => {
                let mut name = vec![id.clone()];
                while let Some(Token::Dot) = self.peek() {
                    self.next(); // consume '.'
                    if let Some(Token::Identifier(next_id)) = self.next() {
                        name.push(next_id);
                    } else {
                        return Err("Expected identifier after '.'".to_string());
                    }
                }
                if let Some(Token::Equal) = self.peek() {
                    self.next(); // consume '='
                    let value = self.parse_expression()?;
                    Ok(Statement::Assign { name, value })
                } else {
                    let expr = self.parse_expression()?;
                    Ok(Statement::Expr(expr))
                }
            }
            Some(Token::LBrace) => {
                self.next(); // consume '{'
                let mut branches = Vec::new();
                loop {
                    let mut statements = Vec::new();
                    while let Some(Token::RBrace) = self.peek() {
                        statements.push(self.parse_statement()?);
                    }
                    self.expect(Token::RBrace)?;

                    let cost = if let Some(Token::LBracket) = self.peek() {
                        self.next(); // consume '['
                        let cost_expr = self.parse_expression()?;
                        self.expect(Token::RBracket)?;
                        cost_expr
                    } else {
                        Expr::Int(1) // default cost
                    };
                    branches.push((statements, cost));
                    if let Some(Token::Or) = self.peek() {
                        self.next(); // consume 'or'
                    } else {
                        break;
                    }
                }
                self.expect(Token::RBrace)?;
                Ok(Statement::Disjunction { disjuncts: branches })
            }
            Some(Token::For) => {
                self.next(); // consume 'for'
                self.expect(Token::LParen)?;
                let var_type = match self.next() {
                    Some(Token::Identifier(type_name)) => vec![type_name],
                    _ => return Err("Expected type name in for loop".to_string()),
                };
                let var_name = match self.next() {
                    Some(Token::Identifier(name)) => name,
                    _ => return Err("Expected variable name in for loop".to_string()),
                };
                self.expect(Token::RParen)?;
                self.expect(Token::LBrace)?;
                let mut statements = Vec::new();
                while let Some(Token::RBrace) = self.peek() {
                    statements.push(self.parse_statement()?);
                }
                self.expect(Token::RBrace)?;
                Ok(Statement::ForAll { var_type, var_name, statements })
            }
            Some(Token::Return) => {
                self.next(); // consume 'return'
                let value = self.parse_expression()?;
                Ok(Statement::Return { value })
            }
            _ => {
                let expr = self.parse_expression()?;
                Ok(Statement::Expr(expr))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse(input: &str) -> Expr {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        parser.parse_expression().expect("Failed to parse expression")
    }

    #[test]
    fn test_literals() {
        assert_eq!(parse("true"), Expr::Bool(true));
        assert_eq!(parse("false"), Expr::Bool(false));
        assert_eq!(parse("123"), Expr::Int(123));
        assert_eq!(parse("12.34"), Expr::Real(1234, 100));
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(parse("foo"), Expr::QualifiedId { ids: vec!["foo".to_string()] });
        assert_eq!(parse("foo.bar"), Expr::QualifiedId { ids: vec!["foo".to_string(), "bar".to_string()] });
    }

    #[test]
    fn test_parentheses() {
        assert_eq!(parse("(123)"), Expr::Int(123));
    }

    #[test]
    fn test_function_calls() {
        assert_eq!(parse("f()"), Expr::Function { name: vec!["f".to_string()], args: vec![] });
        assert_eq!(parse("g(1, true)"), Expr::Function { name: vec!["g".to_string()], args: vec![Expr::Int(1), Expr::Bool(true)] });
        assert_eq!(parse("Math.max(1, 2)"), Expr::Function { name: vec!["Math".to_string(), "max".to_string()], args: vec![Expr::Int(1), Expr::Int(2)] });
    }

    #[test]
    fn test_arithmetic() {
        // 1 + 2
        assert_eq!(parse("1 + 2"), Expr::Sum { terms: vec![Expr::Int(1), Expr::Int(2)] });

        // 1 * 2
        assert_eq!(parse("1 * 2"), Expr::Mul { factors: vec![Expr::Int(1), Expr::Int(2)] });

        // 1 + 2 * 3
        assert_eq!(parse("1 + 2 * 3"), Expr::Sum { terms: vec![Expr::Int(1), Expr::Mul { factors: vec![Expr::Int(2), Expr::Int(3)] },] });

        // (1 + 2) * 3
        assert_eq!(parse("(1 + 2) * 3"), Expr::Mul { factors: vec![Expr::Sum { terms: vec![Expr::Int(1), Expr::Int(2)] }, Expr::Int(3),] });
    }

    #[test]
    fn test_relational() {
        assert_eq!(parse("1 < 2"), Expr::Lt { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse("1 <= 2"), Expr::Leq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse("1 > 2"), Expr::Gt { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse("1 >= 2"), Expr::Geq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse("1 = 1"), Expr::Eq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(1)) });
        assert_eq!(parse("1 != 2"), Expr::Neq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
    }

    #[test]
    fn test_logical() {
        assert_eq!(parse("true & false"), Expr::And { terms: vec![Expr::Bool(true), Expr::Bool(false)] });
        assert_eq!(parse("true | false"), Expr::Or { terms: vec![Expr::Bool(true), Expr::Bool(false)] });

        // n-ary logical ops
        assert_eq!(
            parse("a & b & c"),
            Expr::And {
                terms: vec![Expr::QualifiedId { ids: vec!["a".to_string()] }, Expr::QualifiedId { ids: vec!["b".to_string()] }, Expr::QualifiedId { ids: vec!["c".to_string()] },]
            }
        );

        // Mixed precedence: & binds tighter than |
        assert_eq!(
            parse("a | b & c"),
            Expr::Or {
                terms: vec![
                    Expr::QualifiedId { ids: vec!["a".to_string()] },
                    Expr::And {
                        terms: vec![Expr::QualifiedId { ids: vec!["b".to_string()] }, Expr::QualifiedId { ids: vec!["c".to_string()] },]
                    }
                ]
            }
        );
    }
}
