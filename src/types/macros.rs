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
            fn partial_cmp(&self, o: &$ty_rhs) -> Option<core::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(self.as_ref(), o.as_ref())
            }
        }
        impl PartialOrd<$ty_lhs> for $ty_rhs {
            fn partial_cmp(&self, o: &$ty_lhs) -> Option<core::cmp::Ordering> {
                <$ty_common as PartialOrd<$ty_common>>::partial_cmp(self.as_ref(), o.as_ref())
            }
        }
    };
}

/// Implement conversions and comparisons among different kinds of URI / IRI types.
macro_rules! impl_conv_and_cmp {
    (
        source: {
            owned: $owned:ty,
            slice: $slice:ty,
            creation_error: $ty_creation_error:ident,
            validation_error: $ty_validation_error:ident,
        },
        target: [
        $(
            {
                owned: $target_owned:ty,
                slice: $target_slice:ty,
            }
        ),+ $(,)?
        ],
    ) => {
        $(
            #[cfg(feature = "alloc")]
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

            #[cfg(feature = "alloc")]
            impl core::convert::TryFrom<$target_owned> for $owned {
                type Error = $ty_creation_error<String>;

                fn try_from(v: $target_owned) -> Result<Self, Self::Error> {
                    Self::try_from(Into::<String>::into(v))
                }
            }

            impl<'a> core::convert::TryFrom<&'a $target_slice> for &'a $slice {
                type Error = $ty_validation_error;

                fn try_from(v: &'a $target_slice) -> Result<Self, Self::Error> {
                    Self::try_from(AsRef::<str>::as_ref(v))
                }
            }

            #[cfg(feature = "alloc")]
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

            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, $owned, $target_slice);
            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, $owned, &$target_slice);
            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, $owned, alloc::borrow::Cow<'_, $target_slice>);

            impl_cmp!($target_slice, $slice, $target_slice);
            impl_cmp!($target_slice, $slice, &$target_slice);
            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, $slice, $target_owned);
            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, $slice, alloc::borrow::Cow<'_, $target_slice>);
            impl_cmp!($target_slice, &$slice, $target_slice);
            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, &$slice, $target_owned);
            #[cfg(feature = "alloc")]
            impl_cmp!($target_slice, &$slice, alloc::borrow::Cow<'_, $target_slice>);
        )*
    };
}

/// Implement basic functions and traits for the given URI / IRI types.
///
/// This macro defines spec types which implements `validated_slice::SliceSpec` and
/// `validated_slice::OwnedSliceSpec`.
///
/// * `$slice_spec` and `$owned_spec` should not defined by the other place.
///     + This macro defines these two types.
/// * `$slice` should be defined as `#[repr(transparent)] struct $slice(str);`.
/// * `$owned` should be defined as `struct $owned(String);`.
/// * `$owned_error` should have `$owned_error::new(_: $slice_error, _: String)`.
macro_rules! impl_basics {
    (
        Slice {
            spec: $slice_spec:ident,
            custom: $slice:ident,
            validator: $validator:expr,
            error: $slice_error:ty,
        },
        Owned {
            spec: $owned_spec:ident,
            custom: $owned:ident,
            error: $owned_error:ty,
        },
    ) => {
        /// Spec of the borrowed custom slice.
        enum $slice_spec {}

        impl validated_slice::SliceSpec for $slice_spec {
            type Custom = $slice;
            type Inner = str;
            type Error = $slice_error;

            #[inline]
            fn validate(s: &Self::Inner) -> Result<(), Self::Error> {
                $validator(s)
            }

            validated_slice::impl_slice_spec_methods! {
                field=0;
                methods=[
                    as_inner,
                    as_inner_mut,
                    from_inner_unchecked,
                    from_inner_unchecked_mut,
                ];
            }
        }

        validated_slice::impl_std_traits_for_slice! {
            Std {
                core: core,
                alloc: alloc,
            };
            Spec {
                spec: $slice_spec,
                custom: $slice,
                inner: str,
                error: $slice_error,
            };
            { AsRef<str> };
            { AsRef<{Custom}> };
            { TryFrom<&{Inner}> for &{Custom} };
            { Default for &{Custom} };
            { Display };
        }

        #[cfg(feature = "alloc")]
        validated_slice::impl_std_traits_for_slice! {
            Std {
                core: core,
                alloc: alloc,
            };
            Spec {
                spec: $slice_spec,
                custom: $slice,
                inner: str,
                error: $slice_error,
            };
            { From<&{Custom}> for Arc<{Custom}> };
            { From<&{Custom}> for Box<{Custom}> };
            { From<&{Custom}> for Rc<{Custom}> };
        }

        validated_slice::impl_cmp_for_slice! {
            Std {
                core: core,
                alloc: alloc,
            };
            Spec {
                spec: $slice_spec,
                custom: $slice,
                inner: str,
                base: Inner,
            };
            Cmp { PartialEq, PartialOrd };
            { ({Custom}), (&{Custom}), rev };

            { ({Custom}), ({Inner}), rev };
            { ({Custom}), (&{Inner}), rev };
            { (&{Custom}), ({Inner}), rev };
        }

        #[cfg(feature = "alloc")]
        validated_slice::impl_cmp_for_slice! {
            Std {
                core: core,
                alloc: alloc,
            };
            Spec {
                spec: $slice_spec,
                custom: $slice,
                inner: str,
                base: Inner,
            };
            Cmp { PartialEq, PartialOrd };
            { ({Custom}), (Cow<{Custom}>), rev };

            { ({Custom}), (Cow<{Inner}>), rev };
            { (&{Custom}), (Cow<{Inner}>), rev };
        }

        /// Spec of the owned custom slice.
        #[cfg(feature = "alloc")]
        enum $owned_spec {}

        #[cfg(feature = "alloc")]
        impl validated_slice::OwnedSliceSpec for $owned_spec {
            type Custom = $owned;
            type Inner = String;
            type Error = $owned_error;
            type SliceSpec = $slice_spec;
            type SliceCustom = $slice;
            type SliceInner = str;
            type SliceError = $slice_error;

            #[inline]
            fn convert_validation_error(e: Self::SliceError, v: Self::Inner) -> Self::Error {
                <$owned_error>::new(e, v)
            }

            #[inline]
            fn as_slice_inner(s: &Self::Custom) -> &Self::SliceInner {
                &s.0
            }

            #[inline]
            fn as_slice_inner_mut(s: &mut Self::Custom) -> &mut Self::SliceInner {
                &mut s.0
            }

            #[inline]
            fn inner_as_slice_inner(s: &Self::Inner) -> &Self::SliceInner {
                s
            }

            #[inline]
            unsafe fn from_inner_unchecked(s: Self::Inner) -> Self::Custom {
                $owned(s)
            }

            #[inline]
            fn into_inner(s: Self::Custom) -> Self::Inner {
                s.0
            }
        }

        #[cfg(feature = "alloc")]
        validated_slice::impl_std_traits_for_owned_slice! {
            Std {
                core: core,
                alloc: alloc,
            };
            Spec {
                spec: $owned_spec,
                custom: $owned,
                inner: String,
                error: $owned_error,
                slice_custom: $slice,
                slice_inner: str,
                slice_error: $slice_error,
            };
            { Borrow<str> };
            { Borrow<{SliceCustom}> };
            { ToOwned<Owned = {Custom}> for {SliceCustom} };
            { AsRef<str> };
            { AsRef<{SliceCustom}> };
            { From<{Custom}> for {Inner} };
            { TryFrom<{Inner}> };
            { Display };
            { Deref<Target = {SliceCustom}> };
            { FromStr };
        }

        #[cfg(feature = "alloc")]
        validated_slice::impl_cmp_for_owned_slice! {
            Std {
                core: core,
                alloc: alloc,
            };
            Spec {
                spec: $owned_spec,
                custom: $owned,
                inner: String,
                slice_custom: $slice,
                slice_inner: str,
                base: Inner,
            };
            Cmp { PartialEq, PartialOrd };
            { ({Custom}), ({SliceCustom}), rev };
            { ({Custom}), (&{SliceCustom}), rev };
            { ({Custom}), (Cow<{SliceCustom}>), rev };
            { ({Custom}), ({SliceInner}), rev };
            { ({Custom}), (&{SliceInner}), rev };
            { ({Custom}), (Cow<{SliceInner}>), rev };
        }
    };
}

/// Implement serialization and deserialization with serde.
///
/// * `$expecting`: `&'static str` value.
/// * `$slice`, `$owned`: identifier of the custom slice types.
macro_rules! impl_serde {
    (
        expecting: $expecting:expr,
        slice: $slice:ident,
        owned: $owned:ident,
    ) => {
        #[cfg(feature = "serde")]
        mod __serde {
            use super::{$owned, $slice};

            use core::{convert::TryFrom, fmt};

            use serde::{
                de::{self, Visitor},
                Deserialize, Deserializer,
            };

            /// Custom owned string visitor.
            #[derive(Debug, Clone, Copy)]
            struct CustomStringVisitor;

            impl<'de> Visitor<'de> for CustomStringVisitor {
                type Value = $owned;

                fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.write_str($expecting)
                }

                fn visit_str<E>(self, v: &str) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    <&$slice>::try_from(v)
                        .map(ToOwned::to_owned)
                        .map_err(E::custom)
                }

                fn visit_string<E>(self, v: String) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    <$owned>::try_from(v).map_err(E::custom)
                }
            }

            impl<'de> Deserialize<'de> for $owned {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    deserializer.deserialize_str(CustomStringVisitor)
                }
            }

            /// Custom borrowed string visitor.
            #[derive(Debug, Clone, Copy)]
            struct CustomStrVisitor;

            impl<'de> Visitor<'de> for CustomStrVisitor {
                type Value = &'de $slice;

                fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    f.write_str($expecting)
                }

                fn visit_borrowed_str<E>(self, v: &'de str) -> Result<Self::Value, E>
                where
                    E: de::Error,
                {
                    <&'de $slice>::try_from(v).map_err(E::custom)
                }
            }

            impl<'de: 'a, 'a> Deserialize<'de> for &'a $slice {
                fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
                where
                    D: Deserializer<'de>,
                {
                    deserializer.deserialize_string(CustomStrVisitor)
                }
            }
        }
    };
}
