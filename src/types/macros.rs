//! Macros.

macro_rules! impl_cmp {
    ($ty_common:ty, $ty_lhs:ty, $ty_rhs:ty) => {
        impl PartialEq<$ty_rhs> for $ty_lhs {
            fn eq(&self, o: &$ty_rhs) -> bool {
                <$ty_common as PartialEq<$ty_common>>::eq(self.as_ref(), o.as_ref())
            }
        }
        impl PartialEq<$ty_lhs> for $ty_rhs {
            fn eq(&self, o: &$ty_lhs) -> bool {
                <$ty_common as PartialEq<$ty_common>>::eq(self.as_ref(), o.as_ref())
            }
        }
        impl PartialOrd<$ty_rhs> for $ty_lhs {
            fn partial_cmp(&self, o: &$ty_rhs) -> Option<std::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(self.as_ref(), o.as_ref())
            }
        }
        impl PartialOrd<$ty_lhs> for $ty_rhs {
            fn partial_cmp(&self, o: &$ty_lhs) -> Option<std::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(self.as_ref(), o.as_ref())
            }
        }
    };
}

/// Implement std traits for the given URI / IRI types.
macro_rules! impl_std_traits {
    (
        source: {
            owned: $owned:ty,
            slice: $slice:ty,
            error: $ty_error:ty,
        },
        target: [
        $(
            {
                owned: $target_owned:ty,
                slice: $target_slice:ty,
            }
        ),* $(,)?
        ],
    ) => {
        $(
            impl From<$owned> for $target_owned {
                fn from(s: $owned) -> $target_owned {
                    unsafe {
                        // This should be safe.
                        // Caller of `impl_std_traits` is responsible for that.
                        <$target_owned>::new_unchecked(s.into())
                    }
                }
            }

            impl<'a> From<&'a $slice> for &'a $target_slice {
                fn from(s: &'a $slice) -> &'a $target_slice {
                    s.as_ref()
                }
            }

            impl std::convert::TryFrom<$target_owned> for $owned {
                type Error = $ty_error;

                fn try_from(v: $target_owned) -> Result<Self, Self::Error> {
                    Self::try_from(Into::<String>::into(v))
                }
            }

            impl<'a> std::convert::TryFrom<&'a $target_slice> for &'a $slice {
                type Error = $ty_error;

                fn try_from(v: &'a $target_slice) -> Result<Self, Self::Error> {
                    Self::try_from(AsRef::<str>::as_ref(v))
                }
            }

            impl AsRef<$target_slice> for $owned {
                fn as_ref(&self) -> &$target_slice {
                    AsRef::<$slice>::as_ref(self).as_ref()
                }
            }

            impl AsRef<$target_slice> for $slice {
                fn as_ref(&self) -> &$target_slice {
                    unsafe {
                        // This should be safe.
                        // Caller of `impl_std_traits` is responsible for that.
                        <$target_slice>::new_unchecked(self.as_ref())
                    }
                }
            }

            impl_cmp!($target_slice, $owned, $target_slice);
            impl_cmp!($target_slice, $owned, &$target_slice);
            impl_cmp!($target_slice, $owned, std::borrow::Cow<'_, $target_slice>);

            impl_cmp!($target_slice, $slice, $target_slice);
            impl_cmp!($target_slice, $slice, &$target_slice);
            impl_cmp!($target_slice, $slice, $target_owned);
            impl_cmp!($target_slice, $slice, std::borrow::Cow<'_, $target_slice>);
            impl_cmp!($target_slice, &$slice, $target_slice);
            impl_cmp!($target_slice, &$slice, $target_owned);
            impl_cmp!($target_slice, &$slice, std::borrow::Cow<'_, $target_slice>);
        )*
    };
}
