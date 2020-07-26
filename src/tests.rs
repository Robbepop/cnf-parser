use super::{
    parse_cnf,
    Error,
    Literal,
    Output,
    Problem,
};

#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct StubOutput {
    problem: Option<Problem>,
    head: Vec<Literal>,
    clauses: Vec<Vec<Literal>>,
}

impl StubOutput {
    /// Returns the parsed number of variables if any.
    pub fn num_variables(&self) -> Option<u32> {
        self.problem.map(|problem| problem.num_variables)
    }

    /// Returns the parsed number of clauses if any.
    pub fn num_clauses(&self) -> Option<u32> {
        self.problem.map(|problem| problem.num_clauses)
    }

    /// Asserts that the parsed clauses are the expected ones.
    pub fn assert_clauses(&self, expected: &[&[i32]]) {
        assert!(self.head.is_empty());
        assert_eq!(self.clauses.len(), expected.len());
        for (actual, expected) in self.clauses.iter().zip(expected) {
            assert_eq!(actual.len(), expected.len());
            for (actual, &expected) in actual
                .iter()
                .map(|literal| literal.into_value().get())
                .zip(*expected)
            {
                assert_eq!(actual, expected);
            }
        }
    }
}

impl Output for StubOutput {
    type Error = &'static str;

    fn problem(
        &mut self,
        num_variables: u32,
        num_clauses: u32,
    ) -> Result<(), Self::Error> {
        self.problem = Some(Problem {
            num_variables,
            num_clauses,
        });
        Ok(())
    }

    fn literal(&mut self, literal: crate::Literal) -> Result<(), Self::Error> {
        self.head.push(literal);
        Ok(())
    }

    fn finalize_clause(&mut self) -> Result<(), Self::Error> {
        self.clauses
            .push(core::mem::replace(&mut self.head, Vec::new()));
        Ok(())
    }

    fn finish(&mut self) -> Result<(), Self::Error> {
        if !self.head.is_empty() {
            self.finalize_clause()?;
        }
        Ok(())
    }
}

#[test]
fn simple_cnf_works() {
    let sample = br"
        1 2 0";
    let mut output = StubOutput::default();
    parse_cnf(&mut &sample[..], &mut output).unwrap();
    assert_eq!(output.num_variables(), None);
    assert_eq!(output.num_clauses(), None);
    output.assert_clauses(&[&[1, 2]]);
}

#[test]
fn advanced_cnf_works() {
    let sample = br"
        c Simple example CNF encoded file holding some information
        c and trying to be some kind of a simple test.
        p cnf 42 1337
        1 2 0
        -3 4 0
        5 -6 7 0
        -7 -8 -9 0";
    let mut output = StubOutput::default();
    parse_cnf(&mut &sample[..], &mut output).unwrap();
    assert_eq!(output.num_variables(), Some(42));
    assert_eq!(output.num_clauses(), Some(1337));
    output.assert_clauses(&[&[1, 2], &[-3, 4], &[5, -6, 7], &[-7, -8, -9]]);
}

#[test]
fn literal_just_within_bounds() {
    let sample = br"
        -2147483647 2147483647 0";
    let mut output = StubOutput::default();
    parse_cnf(&mut sample.as_ref(), &mut output).unwrap();
    output.assert_clauses(&[&[-2147483647, 2147483647]]);
}

#[test]
fn literal_out_of_bounds_1() {
    let mut output = StubOutput::default();
    assert_eq!(
        parse_cnf(&mut br"-2147483648 0".as_ref(), &mut output),
        Err(Error::OutOfRangeI32 {
            at: 0,
            encountered: 2147483648,
        })
    );
}

#[test]
fn literal_out_of_bounds_2() {
    let mut output = StubOutput::default();
    assert_eq!(
        parse_cnf(&mut br"2147483648 0".as_ref(), &mut output),
        Err(Error::OutOfRangeI32 {
            at: 0,
            encountered: 2147483648,
        })
    );
}

#[test]
fn duplicate_problem_fails() {
    let sample = br"
        c Failure test with duplicate problem definitions.
        p cnf 5 42
        p cnf 42 5
        1 2 0";
    let mut output = StubOutput::default();
    assert_eq!(
        parse_cnf(&mut sample.as_ref(), &mut output),
        Err(Error::DuplicateProblem {
            at: 87,
            duplicate: Problem {
                num_variables: 42,
                num_clauses: 5
            },
        })
    );
}

#[test]
fn invalid_problem_kind_fails() {
    let sample = br"
        c Failure test where the given problem kind is not supported.
        p sat 5 42
        1 2 0";
    let mut output = StubOutput::default();
    assert_eq!(
        parse_cnf(&mut sample.as_ref(), &mut output),
        Err(Error::UnexpectedByte {
            at: 81,
            encountered: Some(b's'),
            expected: Some(b'c')
        })
    );
}

#[test]
fn problem_num_variables_just_in_range() {
    let sample = br"
        c Failure test where the provided variable number is just within bounds.
        c The number is allowed to be up to u32::MAX (= 4294967295).
        p cnf 4294967295 42
        1 2 0";
    let mut output = StubOutput::default();
    parse_cnf(&mut sample.as_ref(), &mut output).unwrap();
    assert_eq!(output.num_variables(), Some(u32::MAX));
}

#[test]
fn problem_num_variables_out_of_bounds() {
    let sample = br"
        c Failure test where the provided variable number is out of bounds.
        c The number is allowed to be up to u32::MAX (= 4294967295).
        p cnf 4294967296 42
        1 2 0";
    let mut output = StubOutput::default();
    assert_eq!(
        parse_cnf(&mut sample.as_ref(), &mut output),
        Err(Error::OutOfRangeU32 {
            at: 160,
            encountered: 4294967296,
        })
    );
}

#[test]
fn problem_num_clauses_just_in_range() {
    let sample = br"
        c Failure test where the provided clauses number is just within bounds.
        c The number is allowed to be up to u32::MAX (= 4294967295).
        p cnf 5 4294967295
        1 2 0";
    let mut output = StubOutput::default();
    parse_cnf(&mut sample.as_ref(), &mut output).unwrap();
    assert_eq!(output.num_clauses(), Some(u32::MAX));
}

#[test]
fn problem_num_clauses_out_of_bounds() {
    let sample = br"
        c Failure test where the provided clauses number is out of bounds.
        c The number is allowed to be up to u32::MAX (= 4294967295).
        p cnf 5 4294967296
        1 2 0";
    let mut output = StubOutput::default();
    assert_eq!(
        parse_cnf(&mut sample.as_ref(), &mut output),
        Err(Error::OutOfRangeU32 {
            at: 161,
            encountered: 4294967296,
        })
    );
}

#[test]
fn regression_empty_comment() {
    let sample = br"
        c The next comment is empty and the newline directly following the 'c'.
        c The regression we test here was that the next line was skipped.
        c
        p cnf 2 3
    ";
    let mut output = StubOutput::default();
    parse_cnf(&mut sample.as_ref(), &mut output).unwrap();
    assert_eq!(output.num_variables(), Some(2));
    assert_eq!(output.num_clauses(), Some(3));
}

#[test]
#[rustfmt::skip]
fn test_3sat_cnf() {
    let sample = br"
        p cnf 10 4
        1 3 5 0
        -2 -8 6 0
        -4 -8 -1 0
        -10 -7 -2 0
    ";
    let mut output = StubOutput::default();
    parse_cnf(&mut sample.as_ref(), &mut output).unwrap();
    assert_eq!(output.num_variables(), Some(10));
    assert_eq!(output.num_clauses(), Some(4));
    output.assert_clauses(&[
        &[1, 3, 5],
        &[-2, -8, 6],
        &[-4, -8, -1],
        &[-10, -7, -2]
    ]);
}
