//! Stuff for path normalization.

use core::mem;

use crate::buffer::Buffer;
use crate::normalize::{normalize_case_and_pct_encodings, NormalizationType};
use crate::parser::str::{find_split, rfind};
use crate::spec::Spec;

/// Path that is (possibly) not yet processed or being processed.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Path<'a> {
    /// The result. No more processing is needed.
    Done(&'a str),
    /// Not yet completely processed path.
    NeedsProcessing(PathToNormalize<'a>),
}

impl Path<'_> {
    /// Returns the estimated maximum size required for IRI resolution.
    ///
    /// With a buffer of the returned size, IRI resolution (and merge) would
    /// succeed without OOM error. The resolution may succeed with smaller
    /// buffer than this function estimates, but it is not guaranteed.
    ///
    /// Note that this is `O(N)` operation (where N is input length).
    #[must_use]
    pub(super) fn estimate_max_buf_size_for_resolution(&self) -> usize {
        match self {
            Self::Done(s) => s.len(),
            Self::NeedsProcessing(path) => path.estimate_max_buf_size_for_resolution(),
        }
    }
}

/// Path that needs merge and/or dot segment removal.
///
/// If the first string is not empty, it must end with a slash.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PathToNormalize<'a>(Option<&'a str>, &'a str);

impl<'a> PathToNormalize<'a> {
    /// Creates a `PathToNormalize` from the given base and reference paths to be resolved.
    #[must_use]
    pub(crate) fn from_paths_to_be_resolved(base: &'a str, reference: &'a str) -> Self {
        if reference.starts_with('/') {
            return Self(None, reference);
        }

        match rfind(base.as_bytes(), b'/') {
            Some(last_slash_pos) => Self(Some(&base[..=last_slash_pos]), reference),
            None => Self(None, reference),
        }
    }

    /// Creates a `PathToNormalize` from the given single path.
    #[inline]
    #[must_use]
    pub(crate) fn from_single_path(path: &'a str) -> Self {
        Self(None, path)
    }

    /// Returns `true` if empty.
    #[inline]
    #[must_use]
    fn is_empty(&self) -> bool {
        self.0.is_none() && self.1.is_empty()
    }

    /// Returns `true` if the path starts with a slash.
    #[must_use]
    fn starts_with_slash(&self) -> bool {
        self.0.unwrap_or(self.1).starts_with('/')
    }

    /// Prepends a slash to the path.
    ///
    /// # Precondition
    ///
    /// `self.0` should be `None`. If not, this may panic.
    fn prepend_slash(&mut self) {
        assert!(
            self.0.is_none(),
            "[precondition] `prepend_slash()` must be called only when \
             `self.0` is `None`, but it was {:?}",
            self.0
        );
        if self.1.is_empty() {
            self.1 = "/";
        } else {
            self.0 = Some("/");
        }
    }

    /// Trims a leading slash if available.
    ///
    /// Even if there are multiple leading slashes, only one is removed.
    ///
    /// Returns `true` if a leading slash was present.
    fn trim_leading_slash(&mut self) -> bool {
        match &mut self.0 {
            Some(buf) => match buf.strip_prefix('/') {
                Some("") => {
                    self.0 = None;
                    true
                }
                Some(rest) => {
                    *buf = rest;
                    true
                }
                None => false,
            },
            None => match self.1.strip_prefix('/') {
                Some(rest) => {
                    self.1 = rest;
                    true
                }
                None => false,
            },
        }
    }

    /// Pops the first segment, and returns it.
    ///
    /// The returned boolean is whether the segment has a leading slash.
    /// The returned string slice does not contain any slashes.
    fn pop_first_segment(&mut self) -> Option<PathSegment<'a>> {
        if self.is_empty() {
            // Nothing to pop.
            return None;
        }

        // Strip a leading slash if available.
        let leading_slash = self.trim_leading_slash();

        // Choose the buffer to trim the segment from.
        // Note that the first buffer won't be empty if it is not empty now,
        // since it ends with a slash and the segment to be popped don't have
        // a trailing slash.
        let buf: &mut &str = match &mut self.0 {
            Some(buf) => buf,
            None => &mut self.1,
        };

        let segment = match find_split(buf, b'/') {
            Some((segment, rest)) => {
                *buf = rest;
                segment
            }
            None => {
                let segment = mem::take(buf);
                debug_assert_eq!(
                    buf as *const &str, &self.1 as *const &str,
                    "[consistency] the first buffer must not be `Some(\"\")`"
                );
                segment
            }
        };
        Some(PathSegment {
            leading_slash,
            segment,
        })
    }

    /// Runs path normalization.
    ///
    /// This does neither modify nor consume `self` as the function signature
    /// indicates, so this can be called multiple times safely.
    ///
    /// See [RFC 3986 section 5.2.3] for `merge`, and [RFC 3986 section 5.2.4]
    /// for `remove_dot_segments`.
    ///
    /// [RFC 3986 section 5.2.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3
    /// [RFC 3986 section 5.2.4]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4
    pub(super) fn normalize<'b, B: Buffer<'b>, S: Spec>(
        &self,
        buf: &mut B,
        op_norm: NormalizationType,
    ) -> Result<(), B::ExtendError> {
        (*self).normalize_impl::<_, S>(buf, op_norm)
    }

    /// Runs path normalization.
    ///
    /// See [RFC 3986 section 5.2.3] for `merge`, and [RFC 3986 section 5.2.4]
    /// for `remove_dot_segments`.
    ///
    /// [RFC 3986 section 5.2.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3
    /// [RFC 3986 section 5.2.4]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4
    fn normalize_impl<'b, B: Buffer<'b>, S: Spec>(
        mut self,
        buf: &mut B,
        op_norm: NormalizationType,
    ) -> Result<(), B::ExtendError> {
        let path_start = buf.as_bytes().len();

        // Last path segment.
        let mut last_seg_buf: Option<PathSegment<'_>> = None;
        while let Some(next_seg) = self.pop_first_segment() {
            let segkind = next_seg.kind();
            if segkind != SegmentKind::Normal {
                match (
                    next_seg.has_leading_slash(),
                    segkind,
                    self.starts_with_slash(),
                ) {
                    (false, _, false) => {
                        // 2.D (".." or ".").
                        assert!(self.is_empty());
                    }
                    (false, _, true) => {
                        // 2.A ("../" or "./").
                        let is_next_slash_removed = self.trim_leading_slash();
                        assert!(is_next_slash_removed);
                    }
                    (true, SegmentKind::DotDot, is_not_last_seg) => {
                        // 2.C ("/.." or "/../").
                        if !is_not_last_seg {
                            // "/..".
                            assert!(self.is_empty());
                            self.prepend_slash();
                        }
                        pop_last_seg_and_preceding_slash(buf, path_start, &mut last_seg_buf);
                    }
                    (true, SegmentKind::Dot, false) => {
                        // 2.B ("/.").
                        assert!(self.is_empty());
                        self.prepend_slash();
                    }
                    (true, SegmentKind::Dot, true) => {
                        // 2.B ("/./").
                        // Nothing to do.
                    }
                    (_, SegmentKind::Normal, _) => unreachable!("[consistency] already checked"),
                }
            } else {
                // Flush the previous segment.
                if let Some(last_seg) = last_seg_buf.take() {
                    if !last_seg.has_leading_slash() {
                        assert_eq!(buf.as_bytes().len(), path_start);
                    }
                    last_seg.write_to::<_, S>(buf, op_norm)?;
                }
                // Store the last segment.
                last_seg_buf = Some(next_seg);
            }
        }

        // Flush the last segment.
        if let Some(seg) = last_seg_buf.take() {
            if !seg.has_leading_slash() {
                assert_eq!(buf.as_bytes().len(), path_start);
            }
            seg.write_to::<_, S>(buf, op_norm)?;
        }

        Ok(())
    }

    /// Returns the estimated maximum size required for IRI resolution.
    ///
    /// With a buffer of the returned size, IRI resolution (and merge) would
    /// succeed without OOM error. The resolution may succeed with smaller
    /// buffer than this function estimates, but it is not guaranteed.
    ///
    /// Note that this is `O(N)` operation (where N is input length).
    #[inline]
    #[must_use]
    pub(crate) fn estimate_max_buf_size_for_resolution(&self) -> usize {
        let mut this = *self;
        let mut max = 0;
        while let Some(seg) = this.pop_first_segment() {
            if seg.has_leading_slash() {
                max += 1;
            }
            if seg.kind() == SegmentKind::Normal {
                max += seg.segment().len();
            }
        }

        max
    }
}

/// Pops the last path segment and the preceding slash (if any).
fn pop_last_seg_and_preceding_slash<'b, B: Buffer<'b>>(
    buf: &mut B,
    path_start: usize,
    last_seg: &mut Option<PathSegment<'_>>,
) {
    if let Some(seg) = last_seg.take() {
        if !seg.has_leading_slash() {
            // If the last segment does not have leading slash, the path after
            // the pop is empty.
            assert_eq!(buf.as_bytes().len(), path_start);
        }
        // Successfully popped.
        return;
    }

    // Pop a segment from the buffer.
    match rfind(&buf.as_bytes()[path_start..], b'/') {
        Some(slash_pos) => buf.truncate(path_start + slash_pos),
        None => buf.truncate(path_start),
    }
}

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

    /// Returns the segment kind.
    #[must_use]
    fn kind(&self) -> SegmentKind {
        match self.segment {
            "." | "%2E" | "%2e" => SegmentKind::Dot,
            ".." | ".%2E" | ".%2e" | "%2E." | "%2E%2E" | "%2E%2e" | "%2e." | "%2e%2E"
            | "%2e%2e" => SegmentKind::DotDot,
            _ => SegmentKind::Normal,
        }
    }

    /// Writes the segment to the buffer.
    fn write_to<'b, B: Buffer<'b>, S: Spec>(
        &self,
        buf: &mut B,
        op_norm: NormalizationType,
    ) -> Result<(), B::ExtendError> {
        if self.has_leading_slash() {
            buf.push_str("/")?;
        }
        match op_norm {
            NormalizationType::Full => {
                buf.extend_chars(normalize_case_and_pct_encodings::<S>(self.segment()))
            }
            NormalizationType::RemoveDotSegments => buf.push_str(self.segment()),
        }
    }
}

/// Path segment kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SegmentKind {
    /// `.` or the equivalents.
    Dot,
    /// `..` or the equivalents.
    DotDot,
    /// Other normal (not special) segments.
    Normal,
}
