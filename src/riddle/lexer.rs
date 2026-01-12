use std::iter::Peekable;
use std::str::Chars;

#[derive(Debug, PartialEq, Clone)]
pub enum Token {
    Identifier(String),
    Number(String),
    Plus,
    Minus,
    Asterisk,
    Slash,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Equal,
    EqualEqual,
    NotEqual,
    LessThan,
    LessEqual,
    GreaterThan,
    GreaterEqual,
    Semicolon,
    Integer,
    Real,
    String,
    Class,
    Predicate,
    Enum,
    New,
    For,
    This,
    Void,
    Return,
    Fact,
    Goal,
    Or,
    EOF,
}

pub struct Lexer<'a> {
    input: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(input: &'a str) -> Self {
        Lexer {
            input: input.chars().peekable(),
        }
    }

    pub fn next_token(&mut self) -> Token {
        self.skip_whitespace();
        match self.input.peek() {
            Some(&ch) => match ch {
                '+' => {
                    self.input.next();
                    Token::Plus
                }
                '-' => {
                    self.input.next();
                    Token::Minus
                }
                '*' => {
                    self.input.next();
                    Token::Asterisk
                }
                '/' => {
                    self.input.next();
                    Token::Slash
                }
                '(' => {
                    self.input.next();
                    Token::LParen
                }
                ')' => {
                    self.input.next();
                    Token::RParen
                }
                '[' => {
                    self.input.next();
                    Token::LBracket
                }
                ']' => {
                    self.input.next();
                    Token::RBracket
                }
                '{' => {
                    self.input.next();
                    Token::LBrace
                }
                '}' => {
                    self.input.next();
                    Token::RBrace
                }
                ',' => {
                    self.input.next();
                    Token::Comma
                }
                '=' => {
                    self.input.next();
                    if let Some(&'=') = self.input.peek() {
                        self.input.next();
                        Token::EqualEqual
                    } else {
                        Token::Equal
                    }
                }
                '!' => {
                    self.input.next();
                    if let Some(&'=') = self.input.peek() {
                        self.input.next();
                        Token::NotEqual
                    } else {
                        self.next_token()
                    }
                }
                '<' => {
                    self.input.next();
                    if let Some(&'=') = self.input.peek() {
                        self.input.next();
                        Token::LessEqual
                    } else {
                        Token::LessThan
                    }
                }
                '>' => {
                    self.input.next();
                    if let Some(&'=') = self.input.peek() {
                        self.input.next();
                        Token::GreaterEqual
                    } else {
                        Token::GreaterThan
                    }
                }
                ';' => {
                    self.input.next();
                    Token::Semicolon
                }
                '0'..='9' | '.' => self.read_number(),
                'a'..='z' | 'A'..='Z' | '_' => self.read_identifier(),
                _ => {
                    self.input.next();
                    self.next_token()
                }
            },
            None => Token::EOF,
        }
    }

    fn skip_whitespace(&mut self) {
        while let Some(&ch) = self.input.peek() {
            if ch.is_whitespace() {
                self.input.next();
            } else {
                break;
            }
        }
    }

    fn read_number(&mut self) -> Token {
        let mut number = String::new();
        let mut has_decimal_point = false;

        while let Some(&ch) = self.input.peek() {
            if ch.is_digit(10) {
                number.push(ch);
                self.input.next();
            } else if ch == '.' && !has_decimal_point {
                has_decimal_point = true;
                number.push(ch);
                self.input.next();
            } else {
                break;
            }
        }

        Token::Number(number)
    }

    fn read_identifier(&mut self) -> Token {
        let mut identifier = String::new();
        while let Some(&ch) = self.input.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                identifier.push(ch);
                self.input.next();
            } else {
                break;
            }
        }
        match identifier.as_str() {
            "int" => Token::Integer,
            "real" => Token::Real,
            "string" => Token::String,
            "class" => Token::Class,
            "predicate" => Token::Predicate,
            "enum" => Token::Enum,
            "new" => Token::New,
            "for" => Token::For,
            "this" => Token::This,
            "void" => Token::Void,
            "return" => Token::Return,
            "fact" => Token::Fact,
            "goal" => Token::Goal,
            "or" => Token::Or,
            _ => Token::Identifier(identifier),
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Self::Item> {
        let token = self.next_token();
        if token == Token::EOF {
            None
        } else {
            Some(token)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lexer_basic_tokens() {
        let input = "+ - * / ( ) { } [ ] , ; = == != < <= > >= ";
        let mut lexer = Lexer::new(input);
        let expected_tokens = vec![
            Token::Plus,
            Token::Minus,
            Token::Asterisk,
            Token::Slash,
            Token::LParen,
            Token::RParen,
            Token::LBrace,
            Token::RBrace,
            Token::LBracket,
            Token::RBracket,
            Token::Comma,
            Token::Semicolon,
            Token::Equal,
            Token::EqualEqual,
            Token::NotEqual,
            Token::LessThan,
            Token::LessEqual,
            Token::GreaterThan,
            Token::GreaterEqual,
        ];
        for expected in expected_tokens {
            let token = lexer.next_token();
            assert_eq!(token, expected);
        }
    }

    #[test]
    fn test_lexer_identifiers_and_numbers() {
        let input = "var1 var_2 123 45.67";
        let mut lexer = Lexer::new(input);
        let expected_tokens = vec![
            Token::Identifier("var1".to_string()),
            Token::Identifier("var_2".to_string()),
            Token::Number("123".to_string()),
            Token::Number("45.67".to_string()),
        ];
        for expected in expected_tokens {
            let token = lexer.next_token();
            assert_eq!(token, expected);
        }
    }

    #[test]
    fn test_lexer_keywords() {
        let input = "int real string class predicate enum new for this void return fact goal or";
        let mut lexer = Lexer::new(input);
        let expected_tokens = vec![
            Token::Integer,
            Token::Real,
            Token::String,
            Token::Class,
            Token::Predicate,
            Token::Enum,
            Token::New,
            Token::For,
            Token::This,
            Token::Void,
            Token::Return,
            Token::Fact,
            Token::Goal,
            Token::Or,
        ];
        for expected in expected_tokens {
            let token = lexer.next_token();
            assert_eq!(token, expected);
        }
    }
}
