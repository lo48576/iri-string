//! Helpers for characters.

/// Checks if the given character matches `reserved` rule.
#[allow(dead_code)] // TODO
fn is_reserved(c: char) -> bool {
    is_gen_delim(c) || is_sub_delim(c)
}

/// Checks if the given character matches `gen-delim` rule.
#[allow(dead_code)] // TODO
fn is_gen_delim(c: char) -> bool {
    match c {
        ':' | '/' | '?' | '#' | '[' | ']' | '@' => true,
        _ => false,
    }
}

/// Checks if the given character matches `sub-delim` rule.
pub(crate) fn is_sub_delim(c: char) -> bool {
    match c {
        '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '=' => true,
        _ => false,
    }
}

/// Checks if the given character matches `ucschar` rule.
pub(crate) fn is_ucschar(c: char) -> bool {
    match u32::from(c) {
        0xA0..=0xD7FF => true,
        0xF900..=0xFDCF => true,
        0xFDF0..=0xFFEF => true,
        0x1_0000..=0x1_FFFD => true,
        0x2_0000..=0x2_FFFD => true,
        0x3_0000..=0x3_FFFD => true,
        0x4_0000..=0x4_FFFD => true,
        0x5_0000..=0x5_FFFD => true,
        0x6_0000..=0x6_FFFD => true,
        0x7_0000..=0x7_FFFD => true,
        0x8_0000..=0x8_FFFD => true,
        0x9_0000..=0x9_FFFD => true,
        0xA_0000..=0xA_FFFD => true,
        0xB_0000..=0xB_FFFD => true,
        0xC_0000..=0xC_FFFD => true,
        0xD_0000..=0xD_FFFD => true,
        0xE_1000..=0xE_FFFD => true,
        _ => false,
    }
}
