//! `remove_dot_segments` algorithm described in [RCC 3986 5.2.4].
//!
//! [RCC 3986 5.2.4]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4

use core::mem;

use crate::buffer::Buffer;
use crate::normalize::PathSegment;
use crate::parser::str::{find_split, rfind};

/// Path that needs merge and/or dot segment removal.
///
/// If the first string is not empty, it must end with a slash.
#[derive(Clone, Copy)]
pub(crate) struct RemoveDotSegPath<'a>(Option<&'a str>, &'a str);

impl<'a> RemoveDotSegPath<'a> {
    /// Creates a `RemoveDotSegPath` from the given base and reference paths to be resolved.
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

    /// Creates a `RemoveDotSegPath` from the given single path.
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

    /// Runs path `merge` algorithm and `remove_dot_segments` algorithm at once.
    ///
    /// This does neither modify nor consume `self` as the function signature
    /// indicates, so this can be called multiple times safely.
    ///
    /// See [RFC 3986 section 5.2.3] for `merge`, and [RFC 3986 section 5.2.4]
    /// for `remove_dot_segments`.
    ///
    /// [RFC 3986 section 5.2.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3
    /// [RFC 3986 section 5.2.4]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4
    pub(crate) fn merge_and_remove_dot_segments<'b, B: Buffer<'b>>(
        &self,
        buf: &mut B,
    ) -> Result<(), B::ExtendError> {
        (*self).merge_and_remove_dot_segments_impl(buf)
    }

    /// Runs path `merge` algorithm and `remove_dot_segments` algorithm at once.
    ///
    /// See [RFC 3986 section 5.2.3] for `merge`, and [RFC 3986 section 5.2.4]
    /// for `remove_dot_segments`.
    ///
    /// [RFC 3986 section 5.2.3]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.3
    /// [RFC 3986 section 5.2.4]: https://datatracker.ietf.org/doc/html/rfc3986#section-5.2.4
    fn merge_and_remove_dot_segments_impl<'b, B: Buffer<'b>>(
        mut self,
        buf: &mut B,
    ) -> Result<(), B::ExtendError> {
        let path_start = buf.as_bytes().len();

        // Last path segment.
        let mut last_seg_buf: Option<PathSegment<'_>> = None;
        while let Some(next_seg) = self.pop_first_segment() {
            let segname = next_seg.segment();
            let next_seg_is_dot = segname == ".";
            if next_seg_is_dot || segname == ".." {
                match (
                    next_seg.has_leading_slash(),
                    next_seg_is_dot,
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
                    (true, false, is_not_last_seg) => {
                        // 2.C ("/.." or "/../").
                        if !is_not_last_seg {
                            // "/..".
                            assert!(self.is_empty());
                            self.prepend_slash();
                        }
                        pop_last_seg_and_preceding_slash(buf, path_start, &mut last_seg_buf);
                    }
                    (true, true, false) => {
                        // 2.B ("/.").
                        assert!(self.is_empty());
                        self.prepend_slash();
                    }
                    (true, true, true) => {
                        // 2.B ("/./").
                        // Nothing to do.
                    }
                }
            } else {
                // Flush the previous segment.
                if let Some(last_seg) = last_seg_buf.take() {
                    if !last_seg.has_leading_slash() {
                        assert_eq!(buf.as_bytes().len(), path_start);
                    }
                    last_seg.write_to(buf)?;
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
            seg.write_to(buf)?;
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
        /// Segments to be ignored.
        const IGNORE: &[&str] = &[".", ".."];

        let mut this = *self;
        let mut max = 0;
        while let Some(seg) = this.pop_first_segment() {
            if seg.has_leading_slash() {
                max += 1;
            }
            if !IGNORE.contains(&seg.segment()) {
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
