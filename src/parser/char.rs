//! Helpers for characters.

/*
/// Checks if the given character matches `reserved` rule.
fn is_reserved(c: char) -> bool {
    is_gen_delim(c) || is_sub_delim(c)
}

/// Checks if the given character matches `gen-delim` rule.
fn is_gen_delim(c: char) -> bool {
    match c {
        ':' | '/' | '?' | '#' | '[' | ']' | '@' => true,
        _ => false,
    }
}
*/

/// Checks if the given character matches `sub-delim` rule.
pub(crate) fn is_sub_delim(c: char) -> bool {
    matches!(
        c,
        '!' | '$' | '&' | '\'' | '(' | ')' | '*' | '+' | ',' | ';' | '='
    )
}

/// Checks if the given character matches `ucschar` rule.
pub(crate) fn is_ucschar(c: char) -> bool {
    matches!(
        u32::from(c),
        0xA0..=0xD7FF |
        0xF900..=0xFDCF |
        0xFDF0..=0xFFEF |
        0x1_0000..=0x1_FFFD |
        0x2_0000..=0x2_FFFD |
        0x3_0000..=0x3_FFFD |
        0x4_0000..=0x4_FFFD |
        0x5_0000..=0x5_FFFD |
        0x6_0000..=0x6_FFFD |
        0x7_0000..=0x7_FFFD |
        0x8_0000..=0x8_FFFD |
        0x9_0000..=0x9_FFFD |
        0xA_0000..=0xA_FFFD |
        0xB_0000..=0xB_FFFD |
        0xC_0000..=0xC_FFFD |
        0xD_0000..=0xD_FFFD |
        0xE_1000..=0xE_FFFD
    )
}
