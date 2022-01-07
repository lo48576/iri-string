//! Functions for common string operations.

/// Returns the inner string if wrapped.
pub(crate) fn get_wrapped_inner(s: &str, open: u8, close: u8) -> Option<&str> {
    let (prefix, suffix) = match s.as_bytes() {
        [prefix, suffix] | [prefix, .., suffix] => (*prefix, *suffix),
        _ => return None,
    };
    if (prefix == open) && (suffix == close) {
        Some(&s[1..(s.len() - 1)])
    } else {
        None
    }
}

/// Finds the first needle, and returns the string before it and the rest.
///
/// If `needle` is not found, returns `None`.
pub(crate) fn find_split(haystack: &str, needle: u8) -> Option<(&str, &str)> {
    haystack
        .bytes()
        .position(|b| b == needle)
        .map(|pos| haystack.split_at(pos))
}

/// Finds the first needle, and returns the string before it and the rest.
///
/// If no needles are found, returns `None`.
pub(crate) fn find_split2(haystack: &str, needle1: u8, needle2: u8) -> Option<(&str, &str)> {
    haystack
        .bytes()
        .position(|b| b == needle1 || b == needle2)
        .map(|pos| haystack.split_at(pos))
}

/// Finds the first needle, and returns the string before it and the rest.
///
/// If no needles are found, returns `None`.
pub(crate) fn find_split3(
    haystack: &str,
    needle1: u8,
    needle2: u8,
    needle3: u8,
) -> Option<(&str, &str)> {
    haystack
        .bytes()
        .position(|b| b == needle1 || b == needle2 || b == needle3)
        .map(|pos| haystack.split_at(pos))
}

/// Finds the first needle, and returns the string before it and after it.
///
/// If `needle` is not found, returns `None`.
pub(crate) fn find_split_hole(haystack: &str, needle: u8) -> Option<(&str, &str)> {
    haystack
        .bytes()
        .position(|b| b == needle)
        .map(|pos| (&haystack[..pos], &haystack[(pos + 1)..]))
}

/// Finds the first needle, and returns the string before it, the needle, and the string after it.
///
/// If no needles are found, returns `None`.
pub(crate) fn find_split2_hole(
    haystack: &str,
    needle1: u8,
    needle2: u8,
) -> Option<(&str, u8, &str)> {
    haystack
        .bytes()
        .position(|b| b == needle1 || b == needle2)
        .map(|pos| {
            (
                &haystack[..pos],
                haystack.as_bytes()[pos],
                &haystack[(pos + 1)..],
            )
        })
}

/// Finds the first needle, and returns the string before it, the needle, and the string after it.
///
/// If no needles are found, returns `None`.
pub(crate) fn find_split4_hole(
    haystack: &str,
    needle1: u8,
    needle2: u8,
    needle3: u8,
    needle4: u8,
) -> Option<(&str, u8, &str)> {
    haystack
        .bytes()
        .position(|b| b == needle1 || b == needle2 || b == needle3 || b == needle4)
        .map(|pos| {
            (
                &haystack[..pos],
                haystack.as_bytes()[pos],
                &haystack[(pos + 1)..],
            )
        })
}

/// Returns `true` if the string only contains the allowed characters.
fn satisfy_chars<F, G>(mut s: &str, pred_ascii: F, pred_nonascii: G) -> bool
where
    F: Copy + Fn(u8) -> bool,
    G: Copy + Fn(char) -> bool,
{
    while !s.is_empty() {
        match s.bytes().position(|b| !b.is_ascii()) {
            Some(nonascii_pos) => {
                // Valdiate ASCII prefix.
                if nonascii_pos != 0 {
                    let (prefix, rest) = s.split_at(nonascii_pos);
                    if !prefix.bytes().all(pred_ascii) {
                        return false;
                    }
                    s = rest;
                }

                // Extract non-ASCII part and validate it.
                let (prefix, rest) = match s.bytes().position(|b| b.is_ascii()) {
                    Some(ascii_pos) => s.split_at(ascii_pos),
                    None => (s, ""),
                };
                if !prefix.chars().all(pred_nonascii) {
                    return false;
                }
                s = rest;
            }
            None => {
                // All chars are ASCII.
                return s.bytes().all(pred_ascii);
            }
        }
    }

    true
}

/// Returns `true` if the string only contains the allowed characters and percent-encoded char.
pub(crate) fn satisfy_chars_with_pct_encoded<F, G>(
    mut s: &str,
    pred_ascii: F,
    pred_nonascii: G,
) -> bool
where
    F: Copy + Fn(u8) -> bool,
    G: Copy + Fn(char) -> bool,
{
    while let Some((prefix, suffix)) = find_split_hole(s, b'%') {
        // Verify strings before the percent-encoded char.
        if !prefix.is_empty() {
            satisfy_chars(prefix, pred_ascii, pred_nonascii);
        }

        // Verify the percent-encoded char.
        if !starts_with_double_hexdigits(suffix.as_bytes()) {
            return false;
        }

        // Advance the cursor.
        s = &suffix[2..];
    }

    // Verify the rest.
    satisfy_chars(s, pred_ascii, pred_nonascii)
}

/// Returns `true` if the given string starts with two hexadecimal digits.
fn starts_with_double_hexdigits(s: &[u8]) -> bool {
    match s {
        [x, y] | [x, y, ..] => x.is_ascii_hexdigit() && y.is_ascii_hexdigit(),
        _ => false,
    }
}

/// Strips the first character if it is the given ASCII character, and returns the rest.
///
/// # Precondition
///
/// The given ASCII character (`prefix`) should be an ASCII character.
pub(crate) fn strip_ascii_char_prefix(s: &str, prefix: u8) -> Option<&str> {
    debug_assert!(prefix.is_ascii());
    if s.as_bytes().get(0).copied() == Some(prefix) {
        Some(&s[1..])
    } else {
        None
    }
}
