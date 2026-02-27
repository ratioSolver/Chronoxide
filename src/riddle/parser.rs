use crate::riddle::lexer::{Lexer, Token};
use std::{collections::VecDeque, iter::Peekable};

#[derive(Debug, PartialEq)]
pub enum Expr {
    Bool(bool),
    Int(i64),
    Real(i64, i64),
    QualifiedId { ids: Vec<String> },
    Sum { terms: Vec<Expr> },
    Opposite { term: Box<Expr> },
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
    Formula { is_fact: bool, name: String, predicate_name: Vec<String>, args: Vec<(String, Expr)> },
    Return { value: Expr },
}

pub struct Predicate {
    name: String,
    args: Vec<(Vec<String>, String)>,
    statements: Vec<Statement>,
}

pub struct Constructor {
    args: Vec<(Vec<String>, String)>,
    init: Vec<(String, Vec<Expr>)>,
    statements: Vec<Statement>,
}

pub struct Method {
    return_type: Option<Vec<String>>,
    name: String,
    args: Vec<(Vec<String>, String)>,
    statements: Vec<Statement>,
}

pub struct Class {
    name: String,
    parents: Vec<Vec<String>>,
    fields: Vec<(Vec<String>, Vec<String>)>,
    constructors: Vec<Constructor>,
    methods: Vec<Method>,
    predicates: Vec<Predicate>,
}

pub(super) struct Parser<'a> {
    lexer: Peekable<Lexer<'a>>,
    lookahead: VecDeque<Token>,
}

impl<'a> Parser<'a> {
    pub fn new(lexer: Lexer<'a>) -> Self {
        Parser { lexer: lexer.peekable(), lookahead: VecDeque::new() }
    }

    fn peek(&mut self) -> Option<&Token> {
        self.lexer.peek()
    }

    fn peek_n(&mut self, n: usize) -> Option<&Token> {
        while self.lookahead.len() < n {
            if let Some(token) = self.lexer.next() {
                self.lookahead.push_back(token);
            } else {
                break;
            }
        }
        self.lookahead.get(n - 1)
    }

    fn next(&mut self) -> Option<Token> {
        if let Some(token) = self.lookahead.pop_front() { Some(token) } else { self.lexer.next() }
    }

    fn expect(&mut self, expected: Token) -> Result<Token, String> {
        match self.next() {
            Some(token) if token == expected => Ok(token),
            Some(token) => Err(format!("Expected {:?}, found {:?}", expected, token)),
            None => Err(format!("Expected {:?}, found end of input", expected)),
        }
    }

    pub fn parse_class(&mut self) -> Result<Class, String> {
        self.expect(Token::Class)?;
        let name = match self.next() {
            Some(Token::Identifier(name)) => name,
            _ => return Err("Expected class name".to_string()),
        };
        let parents = if let Some(Token::Colon) = self.peek() {
            self.next(); // consume ':'
            let mut parents = Vec::new();
            loop {
                parents.push(self.parse_qualified_id()?);
                if let Some(Token::Comma) = self.peek() {
                    self.next(); // consume ','
                } else {
                    break;
                }
            }
            parents
        } else {
            Vec::new()
        };
        self.expect(Token::LBrace)?;
        let mut fields = Vec::new();
        let mut constructors = Vec::new();
        let mut methods = Vec::new();
        let mut predicates = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            match self.peek() {
                Some(Token::Identifier(id)) if id == &name => constructors.push(self.parse_constructor()?),
                Some(Token::Predicate) => predicates.push(self.parse_predicate()?),
                Some(Token::Void) => methods.push(self.parse_method()?),
                Some(Token::Bool) | Some(Token::Int) | Some(Token::Real) | Some(Token::String) | Some(Token::Identifier(_)) => methods.push(self.parse_method()?),
                _ => return Err("Expected 'constructor', 'predicate', or method definition".to_string()),
            }
        }
        self.expect(Token::RBrace)?;
        Ok(Class { name, parents, fields, constructors, methods, predicates })
    }

    pub fn parse_constructor(&mut self) -> Result<Constructor, String> {
        let _ = match self.next() {
            Some(Token::Identifier(name)) => name,
            _ => return Err("Expected constructor name".to_string()),
        };
        self.expect(Token::LParen)?;
        let mut args = Vec::new();
        while !matches!(self.peek(), Some(Token::RParen)) {
            let arg_type = self.parse_type()?;
            let arg_name = match self.next() {
                Some(Token::Identifier(name)) => name,
                _ => return Err("Expected identifier in constructor arguments".to_string()),
            };
            args.push((arg_type, arg_name));
            if let Some(Token::Comma) = self.peek() {
                self.next(); // consume ','
            } else {
                break;
            }
        }
        self.expect(Token::RParen)?;
        let mut init = Vec::new();
        if let Some(Token::Colon) = self.peek() {
            self.next(); // consume ':'
            while !matches!(self.peek(), Some(Token::LBrace)) {
                let field_name = match self.next() {
                    Some(Token::Identifier(name)) => name,
                    _ => return Err("Expected identifier in constructor initialization".to_string()),
                };
                self.expect(Token::LParen)?;
                let args = self.parse_expr_list()?;
                self.expect(Token::RParen)?;
                init.push((field_name, args));
                if let Some(Token::Comma) = self.peek() {
                    self.next(); // consume ','
                } else {
                    break;
                }
            }
        }
        self.expect(Token::LBrace)?;
        let mut statements = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;
        Ok(Constructor { args, init, statements })
    }

    pub fn parse_method(&mut self) -> Result<Method, String> {
        let return_type = match self.peek() {
            Some(Token::Void) => {
                self.next(); // consume 'void'
                None
            }
            Some(Token::Bool) | Some(Token::Int) | Some(Token::Real) | Some(Token::String) | Some(Token::Identifier(_)) => Some(self.parse_type()?),
            _ => return Err("Expected return type or 'void'".to_string()),
        };
        let name = match self.next() {
            Some(Token::Identifier(name)) => name,
            _ => return Err("Expected method name".to_string()),
        };
        self.expect(Token::LParen)?;
        let mut args = Vec::new();
        while !matches!(self.peek(), Some(Token::RParen)) {
            let arg_type = self.parse_type()?;
            let arg_name = match self.next() {
                Some(Token::Identifier(name)) => name,
                _ => return Err("Expected identifier in method arguments".to_string()),
            };
            args.push((arg_type, arg_name));
            if let Some(Token::Comma) = self.peek() {
                self.next(); // consume ','
            } else {
                break;
            }
        }
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;
        let mut statements = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;
        Ok(Method { return_type, name, args, statements })
    }

    pub fn parse_predicate(&mut self) -> Result<Predicate, String> {
        self.expect(Token::Predicate)?;
        let name = match self.next() {
            Some(Token::Identifier(name)) => name,
            _ => return Err("Expected identifier after 'predicate'".to_string()),
        };
        self.expect(Token::LParen)?;
        let mut args = Vec::new();
        while !matches!(self.peek(), Some(Token::RParen)) {
            let arg_type = self.parse_type()?;
            let arg_name = match self.next() {
                Some(Token::Identifier(name)) => name,
                _ => return Err("Expected identifier in predicate arguments".to_string()),
            };
            args.push((arg_type, arg_name));
            if let Some(Token::Comma) = self.peek() {
                self.next(); // consume ','
            } else {
                break;
            }
        }
        self.expect(Token::RParen)?;
        self.expect(Token::LBrace)?;
        let mut statements = Vec::new();
        while !matches!(self.peek(), Some(Token::RBrace)) {
            statements.push(self.parse_statement()?);
        }
        self.expect(Token::RBrace)?;
        Ok(Predicate { name, args, statements })
    }

    pub fn parse_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        self.parse_or_expression(first)
    }

    fn parse_or_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        let mut terms = vec![self.parse_and_expression(first)?];
        while let Some(Token::Bar) = self.peek() {
            self.next(); // consume '|'
            terms.push(self.parse_and_expression(None)?);
        }
        if terms.len() == 1 { Ok(terms.remove(0)) } else { Ok(Expr::Or { terms }) }
    }

    fn parse_and_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        let mut terms = vec![self.parse_equality_expression(first)?];
        while let Some(Token::Amp) = self.peek() {
            self.next(); // consume '&'
            terms.push(self.parse_equality_expression(None)?);
        }
        if terms.len() == 1 { Ok(terms.remove(0)) } else { Ok(Expr::And { terms }) }
    }

    fn parse_equality_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        let left = self.parse_relational_expression(first)?;
        match self.peek() {
            Some(Token::EqualEqual) => {
                self.next(); // consume '=='
                let right = self.parse_relational_expression(None)?;
                Ok(Expr::Eq { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::NotEqual) => {
                self.next(); // consume '!='
                let right = self.parse_relational_expression(None)?;
                Ok(Expr::Neq { left: Box::new(left), right: Box::new(right) })
            }
            _ => Ok(left),
        }
    }

    fn parse_relational_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        let left = self.parse_additive_expression(first)?;
        match self.peek() {
            Some(Token::LessThan) => {
                self.next(); // consume '<'
                let right = self.parse_additive_expression(None)?;
                Ok(Expr::Lt { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::LessEqual) => {
                self.next(); // consume '<='
                let right = self.parse_additive_expression(None)?;
                Ok(Expr::Leq { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::GreaterThan) => {
                self.next(); // consume '>'
                let right = self.parse_additive_expression(None)?;
                Ok(Expr::Gt { left: Box::new(left), right: Box::new(right) })
            }
            Some(Token::GreaterEqual) => {
                self.next(); // consume '>='
                let right = self.parse_additive_expression(None)?;
                Ok(Expr::Geq { left: Box::new(left), right: Box::new(right) })
            }
            _ => Ok(left),
        }
    }

    fn parse_additive_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        let mut terms = vec![self.parse_multiplicative_expression(first)?];
        while let Some(token) = self.peek() {
            match token {
                Token::Plus => {
                    self.next(); // consume '+'
                    terms.push(self.parse_multiplicative_expression(None)?);
                }
                Token::Minus => {
                    self.next(); // consume '-'
                    let right = self.parse_multiplicative_expression(None)?;
                    terms.push(Expr::Opposite { term: Box::new(right) });
                }
                _ => break,
            }
        }
        if terms.len() == 1 { Ok(terms.remove(0)) } else { Ok(Expr::Sum { terms }) }
    }

    fn parse_multiplicative_expression(&mut self, first: Option<Expr>) -> Result<Expr, String> {
        let mut factors = vec![if let Some(expr) = first { expr } else { self.parse_primary_expression()? }];
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
                    self.expect(Token::LParen)?;
                    let args = self.parse_expr_list()?;
                    self.expect(Token::RParen)?;
                    Ok(Expr::Function { name: ids, args })
                } else {
                    Ok(Expr::QualifiedId { ids })
                }
            }
            Some(Token::LParen) => {
                let expr = self.parse_expression(None)?;
                self.expect(Token::RParen)?;
                Ok(expr)
            }
            Some(token) => Err(format!("Unexpected token: {:?}", token)),
            None => Err("Unexpected end of input".to_string()),
        }
    }

    fn parse_type(&mut self) -> Result<Vec<String>, String> {
        match self.peek() {
            Some(Token::Bool) | Some(Token::Int) | Some(Token::Real) | Some(Token::String) => {
                let type_name = match self.next().unwrap() {
                    Token::Bool => "bool".to_string(),
                    Token::Int => "int".to_string(),
                    Token::Real => "real".to_string(),
                    Token::String => "string".to_string(),
                    _ => unreachable!(),
                };
                return Ok(vec![type_name]);
            }
            Some(Token::Identifier(_)) => self.parse_qualified_id(),
            _ => Err("Expected type name".to_string()),
        }
    }

    fn parse_qualified_id(&mut self) -> Result<Vec<String>, String> {
        let mut ids = match self.next() {
            Some(Token::Identifier(name)) => vec![name],
            _ => return Err("Expected identifier".to_string()),
        };
        while let Some(Token::Dot) = self.peek() {
            self.next(); // consume '.'
            if let Some(Token::Identifier(next_name)) = self.next() {
                ids.push(next_name);
            } else {
                return Err("Expected identifier after '.'".to_string());
            }
        }
        Ok(ids)
    }

    fn parse_expr_list(&mut self) -> Result<Vec<Expr>, String> {
        let mut exprs = Vec::new();
        while !matches!(self.peek(), Some(Token::RParen)) {
            exprs.push(self.parse_expression(None)?);
            if let Some(Token::Comma) = self.peek() {
                self.next(); // consume ','
            } else {
                break;
            }
        }
        Ok(exprs)
    }

    fn parse_var_decl(&mut self) -> Result<(String, Option<Expr>), String> {
        let name = match self.next() {
            Some(Token::Identifier(name)) => name,
            _ => return Err("Expected variable name".to_string()),
        };
        let init_expr = if let Some(Token::Equal) = self.peek() {
            self.next(); // consume '='
            Some(self.parse_expression(None)?)
        } else {
            None
        };
        Ok((name, init_expr))
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
                let mut fields = vec![self.parse_var_decl()?];
                while let Some(Token::Comma) = self.peek() {
                    self.next(); // consume ','
                    fields.push(self.parse_var_decl()?);
                }
                self.expect(Token::Semicolon)?;
                Ok(Statement::LocalField { field_type, fields })
            }
            Some(Token::Identifier(_)) => {
                let ids = self.parse_qualified_id()?;
                match self.peek() {
                    Some(Token::Equal) => {
                        self.next(); // consume '='
                        let value = self.parse_expression(None)?;
                        self.expect(Token::Semicolon)?;
                        Ok(Statement::Assign { name: ids, value })
                    }
                    Some(Token::Identifier(_)) => {
                        let mut fields = vec![self.parse_var_decl()?];
                        while let Some(Token::Comma) = self.peek() {
                            self.next(); // consume ','
                            fields.push(self.parse_var_decl()?);
                        }
                        self.expect(Token::Semicolon)?;
                        Ok(Statement::LocalField { field_type: ids, fields })
                    }
                    _ => {
                        let expr = self.parse_expression(Some(Expr::QualifiedId { ids }))?;
                        self.expect(Token::Semicolon)?;
                        return Ok(Statement::Expr(expr));
                    }
                }
            }
            Some(Token::LBrace) => {
                self.next(); // consume '{'
                let mut branches = Vec::new();
                loop {
                    let mut statements = Vec::new();
                    while !matches!(self.peek(), Some(Token::RBrace)) {
                        statements.push(self.parse_statement()?);
                    }
                    self.expect(Token::RBrace)?;

                    let cost = if let Some(Token::LBracket) = self.peek() {
                        self.next(); // consume '['
                        let cost_expr = self.parse_expression(None)?;
                        self.expect(Token::RBracket)?;
                        cost_expr
                    } else {
                        Expr::Int(1) // default cost
                    };
                    branches.push((statements, cost));
                    if let Some(Token::Or) = self.peek() {
                        self.next(); // consume 'or'
                        self.expect(Token::LBrace)?; // consume '{' for the next branch
                    } else {
                        break;
                    }
                }
                Ok(Statement::Disjunction { disjuncts: branches })
            }
            Some(Token::For) => {
                self.next(); // consume 'for'
                self.expect(Token::LParen)?;
                let var_type = self.parse_type()?;
                let var_name = match self.next() {
                    Some(Token::Identifier(name)) => name,
                    _ => return Err("Expected variable name in for loop".to_string()),
                };
                self.expect(Token::RParen)?;
                self.expect(Token::LBrace)?;
                let mut statements = Vec::new();
                while !matches!(self.peek(), Some(Token::RBrace)) {
                    statements.push(self.parse_statement()?);
                }
                self.expect(Token::RBrace)?;
                Ok(Statement::ForAll { var_type, var_name, statements })
            }
            Some(Token::Return) => {
                self.next(); // consume 'return'
                let value = self.parse_expression(None)?;
                self.expect(Token::Semicolon)?;
                Ok(Statement::Return { value })
            }
            Some(Token::Fact) | Some(Token::Goal) => {
                let is_fact = matches!(self.next(), Some(Token::Fact)); // consume 'fact' or 'goal'
                let name = match self.next() {
                    Some(Token::Identifier(name)) => name,
                    _ => return Err("Expected identifier after 'fact' or 'goal'".to_string()),
                };
                self.expect(Token::Equal)?;
                self.expect(Token::New)?; // consume 'new'
                let predicate_name = self.parse_qualified_id()?;
                self.expect(Token::LParen)?;
                let mut args = Vec::new();
                while !matches!(self.peek(), Some(Token::RParen)) {
                    let arg_name = match self.next() {
                        Some(Token::Identifier(name)) => name,
                        _ => return Err("Expected identifier in formula arguments".to_string()),
                    };
                    self.expect(Token::Colon)?;
                    let arg_expr = self.parse_expression(None)?;
                    args.push((arg_name, arg_expr));
                    if let Some(Token::Comma) = self.peek() {
                        self.next(); // consume ','
                    } else {
                        break;
                    }
                }
                self.expect(Token::RParen)?;
                self.expect(Token::Semicolon)?;
                Ok(Statement::Formula { is_fact, name, predicate_name, args })
            }
            _ => {
                let expr = self.parse_expression(None)?;
                self.expect(Token::Semicolon)?;
                Ok(Statement::Expr(expr))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_expression(input: &str) -> Expr {
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        parser.parse_expression(None).expect("Failed to parse expression")
    }

    #[test]
    fn test_literals() {
        assert_eq!(parse_expression("true"), Expr::Bool(true));
        assert_eq!(parse_expression("false"), Expr::Bool(false));
        assert_eq!(parse_expression("123"), Expr::Int(123));
        assert_eq!(parse_expression("12.34"), Expr::Real(1234, 100));
    }

    #[test]
    fn test_identifiers() {
        assert_eq!(parse_expression("foo"), Expr::QualifiedId { ids: vec!["foo".to_string()] });
        assert_eq!(parse_expression("foo.bar"), Expr::QualifiedId { ids: vec!["foo".to_string(), "bar".to_string()] });
    }

    #[test]
    fn test_parentheses() {
        assert_eq!(parse_expression("(123)"), Expr::Int(123));
    }

    #[test]
    fn test_function_calls() {
        assert_eq!(parse_expression("f()"), Expr::Function { name: vec!["f".to_string()], args: vec![] });
        assert_eq!(parse_expression("g(1, true)"), Expr::Function { name: vec!["g".to_string()], args: vec![Expr::Int(1), Expr::Bool(true)] });
        assert_eq!(parse_expression("Math.max(1, 2)"), Expr::Function { name: vec!["Math".to_string(), "max".to_string()], args: vec![Expr::Int(1), Expr::Int(2)] });
    }

    #[test]
    fn test_arithmetic() {
        // 1 + 2
        assert_eq!(parse_expression("1 + 2"), Expr::Sum { terms: vec![Expr::Int(1), Expr::Int(2)] });

        // 1 * 2
        assert_eq!(parse_expression("1 * 2"), Expr::Mul { factors: vec![Expr::Int(1), Expr::Int(2)] });

        // 1 + 2 * 3
        assert_eq!(parse_expression("1 + 2 * 3"), Expr::Sum { terms: vec![Expr::Int(1), Expr::Mul { factors: vec![Expr::Int(2), Expr::Int(3)] },] });

        // (1 + 2) * 3
        assert_eq!(parse_expression("(1 + 2) * 3"), Expr::Mul { factors: vec![Expr::Sum { terms: vec![Expr::Int(1), Expr::Int(2)] }, Expr::Int(3),] });
    }

    #[test]
    fn test_relational() {
        assert_eq!(parse_expression("1 < 2"), Expr::Lt { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse_expression("1 <= 2"), Expr::Leq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse_expression("1 > 2"), Expr::Gt { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse_expression("1 >= 2"), Expr::Geq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
        assert_eq!(parse_expression("1 == 1"), Expr::Eq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(1)) });
        assert_eq!(parse_expression("1 != 2"), Expr::Neq { left: Box::new(Expr::Int(1)), right: Box::new(Expr::Int(2)) });
    }

    #[test]
    fn test_logical() {
        assert_eq!(parse_expression("true & false"), Expr::And { terms: vec![Expr::Bool(true), Expr::Bool(false)] });
        assert_eq!(parse_expression("true | false"), Expr::Or { terms: vec![Expr::Bool(true), Expr::Bool(false)] });

        // n-ary logical ops
        assert_eq!(
            parse_expression("a & b & c"),
            Expr::And {
                terms: vec![Expr::QualifiedId { ids: vec!["a".to_string()] }, Expr::QualifiedId { ids: vec!["b".to_string()] }, Expr::QualifiedId { ids: vec!["c".to_string()] },]
            }
        );

        // Mixed precedence: & binds tighter than |
        assert_eq!(
            parse_expression("a | b & c"),
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

    #[test]
    fn test_complex_expression() {
        assert_eq!(
            parse_expression("f(x) + 3 * (y - 2) >= 10 & g(z) != 5"),
            Expr::And {
                terms: vec![
                    Expr::Geq {
                        left: Box::new(Expr::Sum {
                            terms: vec![
                                Expr::Function { name: vec!["f".to_string()], args: vec![Expr::QualifiedId { ids: vec!["x".to_string()] }] },
                                Expr::Mul {
                                    factors: vec![
                                        Expr::Int(3),
                                        Expr::Sum {
                                            terms: vec![Expr::QualifiedId { ids: vec!["y".to_string()] }, Expr::Opposite { term: Box::new(Expr::Int(2)) },]
                                        }
                                    ]
                                }
                            ]
                        }),
                        right: Box::new(Expr::Int(10))
                    },
                    Expr::Neq {
                        left: Box::new(Expr::Function { name: vec!["g".to_string()], args: vec![Expr::QualifiedId { ids: vec!["z".to_string()] }] }),
                        right: Box::new(Expr::Int(5))
                    }
                ]
            }
        );
    }

    #[test]
    fn test_predicate() {
        let input = r#"
            predicate isEven(int x) {
                2*x == 0;
            }
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let predicate = parser.parse_predicate().expect("Failed to parse predicate");
        assert_eq!(predicate.name, "isEven");
        assert_eq!(predicate.args, vec![(vec!["int".to_string()], "x".to_string())]);
        assert_eq!(predicate.statements.len(), 1);
        if let Statement::Expr(Expr::Eq { left, right }) = &predicate.statements[0] {
            assert_eq!(**left, Expr::Mul { factors: vec![Expr::Int(2), Expr::QualifiedId { ids: vec!["x".to_string()] }] });
            assert_eq!(**right, Expr::Int(0));
        } else {
            panic!("Expected equality statement in predicate body");
        }
    }

    #[test]
    fn test_constructor() {
        let input = r#"
            Point(int x, int y) : distance(x, y) {
                distance = sqrt(x*x + y*y);
            }
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let constructor = parser.parse_constructor().expect("Failed to parse constructor");
        assert_eq!(constructor.args, vec![(vec!["int".to_string()], "x".to_string()), (vec!["int".to_string()], "y".to_string())]);
        assert_eq!(constructor.init, vec![("distance".to_string(), vec![Expr::QualifiedId { ids: vec!["x".to_string()] }, Expr::QualifiedId { ids: vec!["y".to_string()] }])]);
        assert_eq!(constructor.statements.len(), 1);
        if let Statement::Assign { name, value } = &constructor.statements[0] {
            assert_eq!(name, &vec!["distance".to_string()]);
            assert_eq!(
                *value,
                Expr::Function {
                    name: vec!["sqrt".to_string()],
                    args: vec![Expr::Sum {
                        terms: vec![
                            Expr::Mul {
                                factors: vec![Expr::QualifiedId { ids: vec!["x".to_string()] }, Expr::QualifiedId { ids: vec!["x".to_string()] }]
                            },
                            Expr::Mul {
                                factors: vec![Expr::QualifiedId { ids: vec!["y".to_string()] }, Expr::QualifiedId { ids: vec!["y".to_string()] }]
                            },
                        ]
                    }]
                }
            );
        } else {
            panic!("Expected assignment statement in constructor body");
        }
    }

    #[test]
    fn test_method() {
        let input = r#"
            void move(int dx, int dy) {
                x = x + dx;
                y = y + dy;
            }
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let method = parser.parse_method().expect("Failed to parse method");
        assert_eq!(method.return_type, None);
        assert_eq!(method.name, "move");
        assert_eq!(method.args, vec![(vec!["int".to_string()], "dx".to_string()), (vec!["int".to_string()], "dy".to_string())]);
        assert_eq!(method.statements.len(), 2);
        if let Statement::Assign { name, value } = &method.statements[0] {
            assert_eq!(name, &vec!["x".to_string()]);
            assert_eq!(
                *value,
                Expr::Sum {
                    terms: vec![Expr::QualifiedId { ids: vec!["x".to_string()] }, Expr::QualifiedId { ids: vec!["dx".to_string()] }]
                }
            );
        } else {
            panic!("Expected assignment statement in method body");
        }
        if let Statement::Assign { name, value } = &method.statements[1] {
            assert_eq!(name, &vec!["y".to_string()]);
            assert_eq!(
                *value,
                Expr::Sum {
                    terms: vec![Expr::QualifiedId { ids: vec!["y".to_string()] }, Expr::QualifiedId { ids: vec!["dy".to_string()] }]
                }
            );
        } else {
            panic!("Expected assignment statement in method body");
        }
    }

    #[test]
    fn test_function() {
        let input = r#"
                int add(int a, int b) {
                    return a + b;
                }
            "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let method = parser.parse_method().expect("Failed to parse function");
        assert_eq!(method.return_type, Some(vec!["int".to_string()]));
        assert_eq!(method.name, "add");
        assert_eq!(method.args, vec![(vec!["int".to_string()], "a".to_string()), (vec!["int".to_string()], "b".to_string())]);
        assert_eq!(method.statements.len(), 1);
        if let Statement::Return { value } = &method.statements[0] {
            assert_eq!(
                *value,
                Expr::Sum {
                    terms: vec![Expr::QualifiedId { ids: vec!["a".to_string()] }, Expr::QualifiedId { ids: vec!["b".to_string()] }]
                }
            );
        } else {
            panic!("Expected return statement in function body");
        }
    }

    #[test]
    fn test_disjunction() {
        let input = r#"
            {
                x == 1;
            } or {
                x == 2;
            }
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let statement = parser.parse_statement().expect("Failed to parse disjunction");
        if let Statement::Disjunction { disjuncts } = statement {
            assert_eq!(disjuncts.len(), 2);
            if let Statement::Expr(Expr::Eq { left, right }) = &disjuncts[0].0[0] {
                assert_eq!(**left, Expr::QualifiedId { ids: vec!["x".to_string()] });
                assert_eq!(**right, Expr::Int(1));
            } else {
                panic!("Expected equality statement in first disjunct");
            }
            if let Statement::Expr(Expr::Eq { left, right }) = &disjuncts[1].0[0] {
                assert_eq!(**left, Expr::QualifiedId { ids: vec!["x".to_string()] });
                assert_eq!(**right, Expr::Int(2));
            } else {
                panic!("Expected equality statement in second disjunct");
            }
        } else {
            panic!("Expected disjunction statement");
        }
    }

    #[test]
    fn test_priced_disjunction() {
        let input = r#"
            {
                x == 1;
            } [5] or {
                x == 2;
            } [10.0]
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let statement = parser.parse_statement().expect("Failed to parse priced disjunction");
        if let Statement::Disjunction { disjuncts } = statement {
            assert_eq!(disjuncts.len(), 2);
            assert_eq!(disjuncts[0].1, Expr::Int(5));
            assert_eq!(disjuncts[1].1, Expr::Real(100, 10));
        } else {
            panic!("Expected disjunction statement");
        }
    }

    #[test]
    fn test_for_all() {
        let input = r#"
            for (int i) {
                x == i;
            }
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let statement = parser.parse_statement().expect("Failed to parse for loop");
        if let Statement::ForAll { var_type, var_name, statements } = statement {
            assert_eq!(var_type, vec!["int".to_string()]);
            assert_eq!(var_name, "i");
            assert_eq!(statements.len(), 1);
            if let Statement::Expr(Expr::Eq { left, right }) = &statements[0] {
                assert_eq!(**left, Expr::QualifiedId { ids: vec!["x".to_string()] });
                assert_eq!(**right, Expr::QualifiedId { ids: vec!["i".to_string()] });
            } else {
                panic!("Expected equality statement in for loop body");
            }
        } else {
            panic!("Expected for loop statement");
        }
    }

    #[test]
    fn test_formula() {
        let input = r#"
            fact isEven = new Even(x: 2*x);
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let statement = parser.parse_statement().expect("Failed to parse formula");
        if let Statement::Formula { is_fact, name, predicate_name, args } = statement {
            assert!(is_fact);
            assert_eq!(name, "isEven");
            assert_eq!(predicate_name, vec!["Even".to_string()]);
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].0, "x");
            if let Expr::Mul { factors } = &args[0].1 {
                assert_eq!(factors.len(), 2);
                assert_eq!(factors[0], Expr::Int(2));
                assert_eq!(factors[1], Expr::QualifiedId { ids: vec!["x".to_string()] });
            } else {
                panic!("Expected multiplication expression in formula argument");
            }
        } else {
            panic!("Expected formula statement");
        }
    }

    #[test]
    fn test_complex_statement() {
        let input = r#"
            {
                x == 1;
                for (int i) {
                    y == i;
                }
            } or {
                x == 2;
                for (int j) {
                    y == j;
                }
            } [42.0]
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let statement = parser.parse_statement().expect("Failed to parse complex statement");
        if let Statement::Disjunction { disjuncts } = statement {
            assert_eq!(disjuncts.len(), 2);
            // First disjunct
            assert_eq!(disjuncts[0].1, Expr::Int(1));
            if let Statement::ForAll { var_type, var_name, statements } = &disjuncts[0].0[1] {
                assert_eq!(var_type, &vec!["int".to_string()]);
                assert_eq!(var_name, "i");
                assert_eq!(statements.len(), 1);
                if let Statement::Expr(Expr::Eq { left, right }) = &statements[0] {
                    assert_eq!(**left, Expr::QualifiedId { ids: vec!["y".to_string()] });
                    assert_eq!(**right, Expr::QualifiedId { ids: vec!["i".to_string()] });
                } else {
                    panic!("Expected equality statement in first for loop body");
                }
            } else {
                panic!("Expected for loop in first disjunct");
            }
            // Second disjunct
            assert_eq!(disjuncts[1].1, Expr::Real(420, 10));
            if let Statement::ForAll { var_type, var_name, statements } = &disjuncts[1].0[1] {
                assert_eq!(var_type, &vec!["int".to_string()]);
                assert_eq!(var_name, "j");
                assert_eq!(statements.len(), 1);
                if let Statement::Expr(Expr::Eq { left, right }) = &statements[0] {
                    assert_eq!(**left, Expr::QualifiedId { ids: vec!["y".to_string()] });
                    assert_eq!(**right, Expr::QualifiedId { ids: vec!["j".to_string()] });
                } else {
                    panic!("Expected equality statement in second for loop body");
                }
            } else {
                panic!("Expected for loop in second disjunct");
            }
        }
    }

    #[test]
    fn test_class() {
        let input = r#"
            class Point {
                int x, y;

                void move(int dx, int dy) {
                    x = x + dx;
                    y = y + dy;
                }
            }
        "#;
        let lexer = Lexer::new(input);
        let mut parser = Parser::new(lexer);
        let class = parser.parse_class().expect("Failed to parse class");
        assert_eq!(class.name, "Point");
        assert_eq!(class.fields.len(), 1);
        assert_eq!(class.fields[0].0, vec!["int".to_string()]);
        assert_eq!(class.fields[0].1, vec!["x".to_string(), "y".to_string()]);
        assert_eq!(class.methods.len(), 1);
        let method = &class.methods[0];
        assert_eq!(method.return_type, None);
        assert_eq!(method.name, "move");
        assert_eq!(method.args, vec![(vec!["int".to_string()], "dx".to_string()), (vec!["int".to_string()], "dy".to_string())]);
        assert_eq!(method.statements.len(), 2);
    }
}
