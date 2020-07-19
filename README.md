# CNF Parser

|  Documentation   |       Crates.io      |
|:----------------:|:--------------------:|
| [![docs][1]][2] | [![crates][3]][4]  |

An efficient and customizable parser for the [`.cnf` (Conjunctive Normal Form)][cnf-format]
file format used by [SAT solvers][sat-solving].

- No `unsafe` Rust!
- No dependencies!
- No heap allocations while parsing!
- `no_std` compatible!

## Usage

For parsing use the `parse_cnf` function.
It requires some input source that is expected to be `.cnf` encoded as well
as a `&mut` to a customizable output.
This output needs to implement the `Output` trait and is most probably your solver
or something that initializes your solver from the given `.cnf` input.

### Example

In order to use `parse_cnf` you first have to define your own `Output` type:

```rust
#[derive(Default)]
pub struct MyOutput {
    head_clause: Vec<Literal>,
    clauses: Vec<Vec<Literal>>,
}

impl Output for MyOutput {
    type Error = &'static str;
    fn problem(&mut self, num_variables: u32, num_clauses: u32) -> Result<(), Self::Error> {
        Ok(())
    }
    fn literal(&mut self, literal: Literal) -> Result<(), Self::Error> {
        self.head_clause.push(literal); Ok(())
    }
    fn finalize_clause(&mut self) -> Result<(), Self::Error> {
        self.clauses.push(
            core::mem::replace(&mut self.head_clause, Vec::new())
        ); Ok(())
    }
    fn finish(&mut self) -> Result<(), Self::Error> {
        if !self.head_clause.is_empty() {
            return Err("encountered empty clause")
        }
        self.finalize_clause();
        Ok(())
    }
}
```

Then use `parse_cnf` as follows:

```rust
let my_input: &[u8] = br"
    c This is my input .cnf file with 3 variables and 2 clauses.
    p cnf 3 2
    1 -2 3 0
    1 -3 0
";
let mut my_output = MyOutput::default();
cnf_parser::parse_cnf(&mut my_input.as_ref(), &mut my_output)
    .expect("encountered invalid .cnf input");
```

## License

Licensed under either of

 * Apache license, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Dual licence: [![badge][license-mit-badge]](LICENSE-MIT) [![badge][license-apache-badge]](LICENSE-APACHE)

### Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.

[1]: https://docs.rs/cnf-parser/badge.svg
[2]: https://docs.rs/cnf-parser
[3]: https://img.shields.io/crates/v/cnf-parser.svg
[4]: https://crates.io/crates/cnf-parser

[sat-solving]: https://en.wikipedia.org/wiki/Boolean_satisfiability_problem
[cnf-format]: https://www.cs.utexas.edu/users/moore/acl2/manuals/current/manual/index-seo.php/SATLINK____DIMACS

[license-mit-badge]: https://img.shields.io/badge/license-MIT-blue.svg
[license-apache-badge]: https://img.shields.io/badge/license-APACHE-orange.svg
