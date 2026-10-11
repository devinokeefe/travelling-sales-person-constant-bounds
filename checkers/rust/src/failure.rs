//! How a check ends before it reaches the test of Section 8, and the messages on the way.

use std::io::Write;

/// Writes a line to the standard error stream. The exit status must not depend on whether that
/// stream can be written, so a failure is ignored.
pub fn note(line: &str) {
    let _ = writeln!(std::io::stderr().lock(), "{line}");
}

/// The reason for stopping; `main` turns it into the exit status.
#[derive(Debug)]
pub enum Stop {
    /// A number in the values file differs from the spec file or from the recomputed one: exit
    /// status 1.
    Rejected(String),
    /// A file is unreadable or malformed, the values file has the wrong number of numbers, the
    /// command line is wrong, or an arithmetic bound is violated: exit status 2.
    Invalid(String),
}

/// The result of a step of the check.
pub type Outcome<T> = Result<T, Stop>;

/// Stops with exit status 2.
pub fn invalid<T>(message: String) -> Outcome<T> {
    Err(Stop::Invalid(message))
}

/// Stops with exit status 1.
pub fn rejected<T>(message: String) -> Outcome<T> {
    Err(Stop::Rejected(message))
}
