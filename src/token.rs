use core::num::{
    NonZeroI32,
    NonZeroU32,
};

pub enum Token {
    Problem(Problem),
    Literal(Literal),
    ClauseEnd,
}

impl From<Problem> for Token {
    #[inline]
    fn from(problem: Problem) -> Self {
        Self::Problem(problem)
    }
}

impl From<Literal> for Token {
    #[inline]
    fn from(literal: Literal) -> Self {
        Self::Literal(literal)
    }
}

/// The problem definition.
///
/// This is parsed at most once for every CNF input.
/// Used to hint the underlying solver for the expected number of variables
/// and clauses of the CNF input.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Problem {
    /// The number of variables in the CNF problem.
    pub num_variables: u32,
    /// The number of clauses in the CNF problem.
    pub num_clauses: u32,
}

impl Problem {
    /// Creates a new problem with the given variable and clause numbers.
    pub(crate) fn new(num_variables: u32, num_clauses: u32) -> Self {
        Self {
            num_variables,
            num_clauses,
        }
    }
}

/// A clause literal.
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    value: NonZeroI32,
}

impl Literal {
    /// Creates a new literal from the given `i32` value.
    ///
    /// Returns `None` if `value` is zero.
    pub(crate) fn new(value: NonZeroI32) -> Literal {
        Self { value }
    }

    /// Returns `true` if the literal is positive.
    #[inline]
    pub fn is_positive(self) -> bool {
        self.value.get().is_positive()
    }

    /// Returns `true` if the literal is negative.
    #[inline]
    pub fn is_negative(self) -> bool {
        self.is_positive()
    }

    /// Returns the variable ID of the literal.
    #[inline]
    pub fn variable(self) -> NonZeroU32 {
        NonZeroU32::new(self.value.get().abs() as u32)
            .expect("encountered invalid zero literal")
    }

    /// Returns the raw value representation of the literal.
    #[inline]
    pub fn into_value(self) -> NonZeroI32 {
        self.value
    }
}
