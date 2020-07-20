#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unsafe_code)]

//! An efficient and customizable parser for the
//! [`.cnf` (Conjunctive Normal Form)][cnf-format]
//! file format used by [SAT solvers][sat-solving].
//!
//! [sat-solving]: https://en.wikipedia.org/wiki/Boolean_satisfiability_problem
//! [cnf-format]: https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SATLINK____DIMACS
//!
//! # Usage
//!
//! ```
//! # use cnf_parser::{Literal, Output};
//!
//! #[derive(Default)]
//! pub struct MyOutput {
//!     head_clause: Vec<Literal>,
//!     clauses: Vec<Vec<Literal>>,
//! }
//!
//! impl Output for MyOutput {
//!     type Error = &'static str;
//!
//!     fn problem(&mut self, num_variables: u32, num_clauses: u32) -> Result<(), Self::Error> {
//!         Ok(())
//!     }
//!
//!     fn literal(&mut self, literal: Literal) -> Result<(), Self::Error> {
//!         self.head_clause.push(literal); Ok(())
//!     }
//!
//!     fn finalize_clause(&mut self) -> Result<(), Self::Error> {
//!         if self.head_clause.is_empty() {
//!             return Err("encountered empty clause")
//!         }
//!         self.clauses.push(
//!             core::mem::replace(&mut self.head_clause, Vec::new())
//!         );
//!         Ok(())
//!     }
//!
//!     fn finish(&mut self) -> Result<(), Self::Error> {
//!         if !self.head_clause.is_empty() {
//!             self.finalize_clause()?
//!         }
//!         Ok(())
//!     }
//! }
//!
//! let my_input: &[u8] = br"
//!     c This is my input .cnf file with 3 variables and 2 clauses.
//!     p cnf 3 2
//!     1 -2 3 0
//!     1 -3 0
//! ";
//! let mut my_output = MyOutput::default();
//! cnf_parser::parse_cnf(&mut my_input.as_ref(), &mut my_output)
//!     .expect("encountered invalid .cnf input");
//! ```

mod lexer;
mod token;

#[cfg(test)]
mod tests;

pub use self::{
    lexer::Error,
    token::{
        Literal,
        Problem,
    },
};
use self::{
    lexer::Lexer,
    token::Token,
};

/// Types that can be used as input for the CNF parser.
pub trait Input {
    /// Reads a byte from the input if any is remaining.
    fn read_byte(&mut self) -> Option<u8>;
}

impl<'a> Input for &'a [u8] {
    fn read_byte(&mut self) -> Option<u8> {
        let len = self.len();
        if len == 0 {
            return None
        }
        let byte = self[0];
        *self = &self[1..];
        Some(byte)
    }
}

/// Input wrapper for [`T: Read`](https://doc.rust-lang.org/std/io/trait.Read.html)
/// types.
///
/// # Note
///
/// This type is only available if the crate has been compiled with the `std`
/// crate feature.
#[cfg(feature = "std")]
pub struct IoReader<R>(pub R)
where
    R: std::io::Read;

#[cfg(feature = "std")]
impl<R> Input for IoReader<R>
where
    R: std::io::Read,
{
    fn read_byte(&mut self) -> Option<u8> {
        let mut buf = [0x00];
        self.0.read_exact(&mut buf).ok().map(|_| buf[0])
    }
}

/// The output where the CNF information is piped to.
///
/// Usually implemented by a dependency of this crate.
pub trait Output {
    /// An error that can occure with the parser output.
    type Error;

    /// The optional problem line with the number of total variables and clauses.
    ///
    /// # Note
    ///
    /// This will only be processed once per CNF input stream.
    fn problem(
        &mut self,
        num_variables: u32,
        num_clauses: u32,
    ) -> Result<(), Self::Error>;

    /// A literal has been read.
    fn literal(&mut self, literal: Literal) -> Result<(), Self::Error>;

    /// The end of the current clause has been read.
    fn finalize_clause(&mut self) -> Result<(), Self::Error>;

    /// Called at the end of CNF parsing.
    ///
    /// Outputs can expect to receive no more messages from the parser after
    /// being called with `finish`.
    fn finish(&mut self) -> Result<(), Self::Error>;
}

/// Parses a CNF formatted input stream into the given output.
///
/// # Errors
///
/// - If the CNF input is malformed.
/// - If the output triggers a custom error.
pub fn parse_cnf<I, O>(
    input: &mut I,
    output: &mut O,
) -> Result<(), Error<<O as Output>::Error>>
where
    I: Input,
    O: Output,
{
    let mut lexer = <Lexer<I, O>>::new(input);
    loop {
        match lexer.next_token()? {
            Some(Token::Problem(problem)) => {
                output
                    .problem(problem.num_variables, problem.num_clauses)
                    .map_err(Error::from_output)?
            }
            Some(Token::Literal(literal)) => {
                output.literal(literal).map_err(Error::from_output)?
            }
            Some(Token::ClauseEnd) => {
                output.finalize_clause().map_err(Error::from_output)?
            }
            None => break,
        }
    }
    output.finish().map_err(Error::from_output)?;
    Ok(())
}
