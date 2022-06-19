//! Utilities for formatting.

use core::fmt::{self, Write as _};

/// Returns true if the two equals after they are converted to strings.
pub(crate) fn eq_str_display<T>(s: &str, d: &T) -> bool
where
    T: ?Sized + fmt::Display,
{
    /// Dummy writer to compare the formatted object to the given string.
    struct CmpWriter<'a>(&'a str);
    impl fmt::Write for CmpWriter<'_> {
        fn write_str(&mut self, s: &str) -> fmt::Result {
            if self.0.len() < s.len() {
                return Err(fmt::Error);
            }
            let (prefix, rest) = self.0.split_at(s.len());
            self.0 = rest;
            if prefix == s {
                Ok(())
            } else {
                Err(fmt::Error)
            }
        }
    }

    let mut writer = CmpWriter(s);
    let succeeded = write!(writer, "{}", d).is_ok();
    succeeded && writer.0.is_empty()
}

/// A debug-printable type to hide the sensitive information.
#[derive(Clone, Copy)]
pub(crate) struct Censored;

impl core::fmt::Debug for Censored {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("{censored}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn eq_str_display_1() {
        assert!(eq_str_display("hello", "hello"));
        assert!(eq_str_display("42", &42));

        assert!(eq_str_display(
            r#"\x00\t\r\n\xff\\"#,
            &b"\x00\t\r\n\xff\\".escape_ascii()
        ));

        assert!(!eq_str_display("hello", "world"));
        assert!(!eq_str_display("hello world", "hello"));
        assert!(!eq_str_display("hello", "hello world"));
        assert!(!eq_str_display("42", &4));
        assert!(!eq_str_display("4", &42));
    }
}
