use crate::riddle::lexer::{Lexer, Token};
use std::iter::Peekable;

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
}
