//! Parse and validate.
use iri_string::{
    spec::{IriSpec, UriSpec},
    types::*,
    validate,
};

mod utils;

macro_rules! define_tests {
    ($positive:ident, $negative:ident, ($spec:ident, $kind:ident), $slice:ty, $owned:ty, $validator:path,) => {
        define_tests! {
            @positive,
            $positive,
            ($spec, $kind),
            $slice,
            $owned,
            $validator,
        }
        define_tests! {
            @negative,
            $negative,
            ($spec, $kind),
            $slice,
            $owned,
            $validator,
        }
    };
    (@positive, $name:ident, ($spec:ident, $kind:ident), $slice:ty, $owned:ty, $validator:path,) => {
        #[test]
        fn $name() {
            for s in utils::positive(utils::Spec::$spec, utils::Kind::$kind) {
                assert!(<$slice>::new(s).is_ok(), "{:?}", s);
                assert!($validator(s).is_ok(), "{:?}", s);
            }
        }
    };
    (@negative, $name:ident, ($spec:ident, $kind:ident), $slice:ty, $owned:ty, $validator:path,) => {
        #[test]
        fn $name() {
            for s in utils::negative(utils::Spec::$spec, utils::Kind::$kind) {
                assert!(<$slice>::new(s).is_err(), "{:?}", s);
                assert!($validator(s).is_err(), "{:?}", s);
            }
        }
    };
}

define_tests! {
    uri,
    not_uri,
    (Uri, Normal),
    UriStr,
    UriString,
    validate::iri::<UriSpec>,
}

define_tests! {
    uri_absolute,
    not_uri_absolute,
    (Uri, Absolute),
    UriAbsoluteStr,
    UriAbsoluteString,
    validate::absolute_iri::<UriSpec>,
}

define_tests! {
    uri_reference,
    not_uri_reference,
    (Uri, Reference),
    UriReferenceStr,
    UriReferenceString,
    validate::iri_reference::<UriSpec>,
}

define_tests! {
    uri_relative,
    not_uri_relative,
    (Uri, Relative),
    UriRelativeStr,
    UriRelativeString,
    validate::relative_ref::<UriSpec>,
}

define_tests! {
    iri,
    not_iri,
    (Iri, Normal),
    IriStr,
    IriString,
    validate::iri::<IriSpec>,
}

define_tests! {
    iri_absolute,
    not_iri_absolute,
    (Iri, Absolute),
    IriAbsoluteStr,
    IriAbsoluteString,
    validate::absolute_iri::<IriSpec>,
}

define_tests! {
    iri_reference,
    not_iri_reference,
    (Iri, Reference),
    IriReferenceStr,
    IriReferenceString,
    validate::iri_reference::<IriSpec>,
}

define_tests! {
    iri_relative,
    not_iri_relative,
    (Iri, Relative),
    IriRelativeStr,
    IriRelativeString,
    validate::relative_ref::<IriSpec>,
}
