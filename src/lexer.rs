use crate::{
    Input,
    Literal,
    Output,
    Problem,
    Token,
};
use core::{
    marker::PhantomData,
    num::NonZeroI32,
};

/// A parse buffer helping with reading bytes from an input source.
pub struct PeekReader<'a, I> {
    input: &'a mut I,
    peek: Option<u8>,
    current: usize,
}

impl<'a, I> PeekReader<'a, I>
where
    I: Input,
{
    /// Creates a new parse buffer from the given slice of bytes.
    pub fn new(input: &'a mut I) -> Self {
        Self {
            input,
            peek: None,
            current: 0,
        }
    }

    /// Returns the current position in the input stream.
    ///
    /// # Note
    ///
    /// This is mostly important for error handling information.
    pub fn current_position(&self) -> usize {
        self.current.saturating_sub(1)
    }

    /// Peeks the next byte from the source if any bytes are left.
    pub fn peek_byte(&mut self) -> Option<u8> {
        match self.peek {
            Some(peek) => Some(peek),
            None => self.read_byte(),
        }
    }

    /// Skips the next byte.
    pub fn skip_byte(&mut self) {
        match &mut self.peek {
            None => {
                self.read_byte();
            }
            peek @ Some(_) => {
                *peek = None;
            }
        }
    }

    /// Reads the next byte from the source if any bytes are left.
    pub fn read_byte(&mut self) -> Option<u8> {
        self.peek = self.input.read_byte();
        if self.peek.is_some() {
            self.current += 1;
        }
        self.peek
    }
}

/// Errors encountered while parsing CNF input.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error<OutputError> {
    Output(OutputError),
    UnexpectedByte {
        at: usize,
        encountered: Option<u8>,
        expected: Option<u8>,
    },
    InvalidTokenStart {
        at: usize,
        encountered: u8,
    },
    ExpectedWhitespace {
        at: usize,
        encountered: Option<u8>,
    },
    OutOfRangeU32 {
        at: usize,
        encountered: u64,
    },
    OutOfRangeI32 {
        at: usize,
        encountered: u32,
    },
    DuplicateProblem {
        at: usize,
        duplicate: Problem,
    },
}

impl<OutputError> Error<OutputError> {
    pub(crate) fn from_output(output_error: OutputError) -> Self {
        Self::Output(output_error)
    }
}

/// A CNF lexer and parser.
pub struct Lexer<'a, I, O> {
    reader: PeekReader<'a, I>,
    seen_problem: bool,
    marker: PhantomData<fn() -> O>,
}

impl<'a, I, O> Lexer<'a, I, O>
where
    I: Input + 'a,
    O: Output,
{
    pub fn new(input: &'a mut I) -> Self {
        Self {
            reader: PeekReader::new(input),
            seen_problem: false,
            marker: Default::default(),
        }
    }

    fn is_nonzero_i32_start(byte: u8) -> bool {
        match byte {
            b'-' | b'1'..=b'9' => true,
            _ => false,
        }
    }

    fn parse_nonzero_i32(&mut self) -> Result<NonZeroI32, Error<<O as Output>::Error>> {
        debug_assert!(self
            .reader
            .peek_byte()
            .map(Self::is_nonzero_i32_start)
            .unwrap_or(false));
        let pos = self.reader.current_position();
        let sign_factor = if self.reader.peek_byte() == Some(b'-') {
            self.reader.read_byte();
            -1
        } else {
            1
        };
        let value_u32 = self.parse_u32()?;
        if value_u32 > i32::MAX as u32 || value_u32 == 0 {
            return Err(Error::OutOfRangeI32 {
                at: pos,
                encountered: value_u32,
            })
        }
        let value_i32 = value_u32 as i32 * sign_factor;
        Ok(NonZeroI32::new(value_i32).expect("encountered invalid zero i32 value"))
    }

    fn is_literal_start(byte: u8) -> bool {
        Self::is_nonzero_i32_start(byte)
    }

    fn parse_literal(&mut self) -> Result<Literal, Error<<O as Output>::Error>> {
        debug_assert!(self
            .reader
            .peek_byte()
            .map(Self::is_literal_start)
            .unwrap_or(false));
        let value = self.parse_nonzero_i32()?;
        Ok(Literal::new(value))
    }

    fn parse_u32(&mut self) -> Result<u32, Error<<O as Output>::Error>> {
        debug_assert!(self
            .reader
            .peek_byte()
            .map(|c| c.is_ascii_digit())
            .unwrap_or(false));
        let pos = self.reader.current_position();
        let mut acc: u64 = 0;
        'outer: loop {
            match self.reader.peek_byte() {
                None => break 'outer,
                Some(c) if c.is_ascii_whitespace() => break 'outer,
                Some(c) if c.is_ascii_digit() => {
                    self.reader.skip_byte();
                    let normalized = c - b'0';
                    acc *= 10;
                    acc += normalized as u64;
                    if acc > u32::MAX as u64 {
                        return Err(Error::OutOfRangeU32 {
                            at: pos,
                            encountered: acc,
                        })
                    }
                }
                Some(invalid) => {
                    return Err(Error::UnexpectedByte {
                        at: self.reader.current_position(),
                        encountered: Some(invalid),
                        expected: None,
                    })
                }
            }
        }
        Ok(acc as u32)
    }

    fn skip_expected_str(
        &mut self,
        str: &str,
    ) -> Result<(), Error<<O as Output>::Error>> {
        for &expected in str.as_bytes() {
            let actual = self.reader.peek_byte();
            if actual != Some(expected) {
                return Err(Error::UnexpectedByte {
                    at: self.reader.current_position(),
                    encountered: actual,
                    expected: Some(expected),
                })
            } else {
                self.reader.skip_byte();
            }
        }
        Ok(())
    }

    /// Skips all bytes until a non ascii whitespace byte is peeked.
    ///
    /// Returns `true` if whitespace has actually been skipped.
    fn skip_whitespace(&mut self) -> bool {
        let mut skipped_whitespace = false;
        'skip: loop {
            match self.reader.peek_byte() {
                Some(whitespace) if whitespace.is_ascii_whitespace() => {
                    self.reader.skip_byte();
                    skipped_whitespace = true;
                    continue 'skip
                }
                _non_whitespace => return skipped_whitespace,
            }
        }
    }

    fn skip_expected_whitespace(&mut self) -> Result<(), Error<<O as Output>::Error>> {
        if !self.skip_whitespace() {
            return Err(Error::ExpectedWhitespace {
                at: self.reader.current_position(),
                encountered: self.reader.peek_byte(),
            })
        }
        Ok(())
    }

    fn parse_problem(&mut self) -> Result<Problem, Error<<O as Output>::Error>> {
        debug_assert_eq!(self.reader.peek_byte(), Some(b'p'));
        let pos = self.reader.current_position();
        self.reader.skip_byte();
        self.skip_expected_whitespace()?;
        self.skip_expected_str("cnf")?;
        self.skip_expected_whitespace()?;
        let num_variables = self.parse_u32()?;
        self.skip_expected_whitespace()?;
        let num_clauses = self.parse_u32()?;
        let problem = Problem::new(num_variables, num_clauses);
        if self.seen_problem {
            return Err(Error::DuplicateProblem {
                at: pos,
                duplicate: problem,
            })
        }
        self.seen_problem = true;
        Ok(problem)
    }

    fn skip_comment(&mut self) -> Result<(), Error<<O as Output>::Error>> {
        debug_assert_eq!(self.reader.peek_byte(), Some(b'c'));
        self.reader.skip_byte();
        self.skip_expected_whitespace()?;
        'skip: loop {
            match self.reader.peek_byte() {
                None | Some(b'\n') => return Ok(()),
                Some(_other) => {
                    self.reader.skip_byte();
                    continue 'skip
                }
            }
        }
    }

    fn parse_end_clause(&mut self) -> Result<Token, Error<<O as Output>::Error>> {
        debug_assert_eq!(self.reader.peek_byte(), Some(b'0'));
        self.reader.skip_byte();
        Ok(Token::ClauseEnd)
    }

    /// Returns the next input token if any.
    ///
    /// # Errors
    ///
    /// Returns an error in case the input is malformatted.
    pub fn next_token(&mut self) -> Result<Option<Token>, Error<<O as Output>::Error>> {
        self.skip_whitespace();
        match self.reader.peek_byte() {
            None => Ok(None),
            Some(b'p') => self.parse_problem().map(Token::from).map(Into::into),
            Some(b'c') => {
                self.skip_comment()?;
                self.next_token()
            }
            Some(b'0') => self.parse_end_clause().map(Into::into),
            Some(byte) if Self::is_literal_start(byte) => {
                self.parse_literal().map(Token::from).map(Into::into)
            }
            Some(invalid) => {
                Err(Error::InvalidTokenStart {
                    at: self.reader.current_position(),
                    encountered: invalid,
                })
            }
        }
    }
}
