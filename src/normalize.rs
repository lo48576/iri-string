//! Normalization.

mod remove_dot_segments;

use crate::buffer::Buffer;

pub(crate) use self::remove_dot_segments::RemoveDotSegPath;

/// A segment with optional leading slash.
#[derive(Clone, Copy)]
struct PathSegment<'a> {
    /// Presence of a leading slash.
    leading_slash: bool,
    /// Segment name (without any slashes).
    segment: &'a str,
}

impl<'a> PathSegment<'a> {
    /// Returns `true` if the segment has a leading slash.
    #[inline]
    #[must_use]
    fn has_leading_slash(&self) -> bool {
        self.leading_slash
    }

    /// Returns the segment without any slashes.
    #[inline]
    #[must_use]
    fn segment(&self) -> &'a str {
        self.segment
    }

    /// Writes the segment to the buffer.
    fn write_to<'b, B: Buffer<'b>>(&self, buf: &mut B) -> Result<(), B::ExtendError> {
        if self.has_leading_slash() {
            buf.push_str("/")?;
        }
        buf.push_str(self.segment())
    }
}
