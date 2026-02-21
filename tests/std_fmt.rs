use iri_string::format::write_to_slice;
use iri_string::template::UriTemplateStr;
#[cfg(feature = "alloc")]
use iri_string::template::UriTemplateString;
use iri_string::types::{
    IriAbsoluteStr, IriFragmentStr, IriQueryStr, IriReferenceStr, IriRelativeStr, IriStr,
};
#[cfg(feature = "alloc")]
use iri_string::types::{
    IriAbsoluteString, IriFragmentString, IriQueryString, IriReferenceString, IriRelativeString,
    IriString,
};

fn check_fill_align<T: core::fmt::Display + AsRef<str>>(iri: T) {
    const BUF_SIZE: usize = 64;
    let mut buf_iri = [0_u8; BUF_SIZE];
    let mut buf_str = [0_u8; BUF_SIZE];

    let s: &str = iri.as_ref();

    assert_eq!(
        write_to_slice(&mut buf_iri, &format_args!("{:48}", iri)).unwrap(),
        write_to_slice(&mut buf_str, &format_args!("{:48}", s)).unwrap()
    );
    assert_eq!(
        write_to_slice(&mut buf_iri, &format_args!("{:[<48}", iri)).unwrap(),
        write_to_slice(&mut buf_str, &format_args!("{:[<48}", s)).unwrap()
    );
    assert_eq!(
        write_to_slice(&mut buf_iri, &format_args!("{:>48}", iri)).unwrap(),
        write_to_slice(&mut buf_str, &format_args!("{:>48}", s)).unwrap()
    );
    assert_eq!(
        write_to_slice(&mut buf_iri, &format_args!("{:]>48}", iri)).unwrap(),
        write_to_slice(&mut buf_str, &format_args!("{:]>48}", s)).unwrap()
    );
    assert_eq!(
        write_to_slice(&mut buf_iri, &format_args!("{:^48}", iri)).unwrap(),
        write_to_slice(&mut buf_str, &format_args!("{:^48}", s)).unwrap()
    );
    assert_eq!(
        write_to_slice(&mut buf_iri, &format_args!("{:|^48}", iri)).unwrap(),
        write_to_slice(&mut buf_str, &format_args!("{:|^48}", s)).unwrap()
    );
}

#[test]
fn fill_align() {
    check_fill_align(IriReferenceStr::new("a://b/c?d#e").unwrap());
    check_fill_align(IriReferenceStr::new("a:///c?d#e").unwrap());
    check_fill_align(IriReferenceStr::new("a:b/c?d#e").unwrap());
    check_fill_align(IriReferenceStr::new("//b/c?d#e").unwrap());
    check_fill_align(IriReferenceStr::new("///c?d#e").unwrap());
    check_fill_align(IriReferenceStr::new("b/c?d#e").unwrap());

    check_fill_align(IriStr::new("a://b/c?d#e").unwrap());
    check_fill_align(IriStr::new("a:///c?d#e").unwrap());
    check_fill_align(IriStr::new("a:b/c?d#e").unwrap());

    check_fill_align(IriAbsoluteStr::new("a://b/c?d").unwrap());
    check_fill_align(IriAbsoluteStr::new("a:///c?d").unwrap());
    check_fill_align(IriAbsoluteStr::new("a:b/c?d").unwrap());

    check_fill_align(IriRelativeStr::new("//b/c?d#e").unwrap());
    check_fill_align(IriRelativeStr::new("///c?d#e").unwrap());
    check_fill_align(IriRelativeStr::new("b/c?d#e").unwrap());

    check_fill_align(IriFragmentStr::new("").unwrap());
    check_fill_align(IriFragmentStr::new("frag").unwrap());

    check_fill_align(IriQueryStr::new("").unwrap());
    check_fill_align(IriQueryStr::new("query").unwrap());
    check_fill_align(IriQueryStr::new("a=b&a=c&d=e").unwrap());

    check_fill_align(IriQueryStr::new("").unwrap());
    check_fill_align(IriQueryStr::new("query").unwrap());
    check_fill_align(IriQueryStr::new("a=b&a=c&d=e").unwrap());

    check_fill_align(UriTemplateStr::new("").unwrap());
    check_fill_align(UriTemplateStr::new("a://b/c?d#e").unwrap());
    check_fill_align(
        UriTemplateStr::new("{scheme}://www{.domain*}{/path*}{?query}{#frag*}").unwrap(),
    );
}

#[cfg(feature = "alloc")]
#[test]
fn fill_align_alloc() {
    check_fill_align(IriReferenceString::try_from("a://b/c?d#e").unwrap());
    check_fill_align(IriReferenceString::try_from("a:///c?d#e").unwrap());
    check_fill_align(IriReferenceString::try_from("a:b/c?d#e").unwrap());
    check_fill_align(IriReferenceString::try_from("//b/c?d#e").unwrap());
    check_fill_align(IriReferenceString::try_from("///c?d#e").unwrap());
    check_fill_align(IriReferenceString::try_from("b/c?d#e").unwrap());

    check_fill_align(IriString::try_from("a://b/c?d#e").unwrap());
    check_fill_align(IriString::try_from("a:///c?d#e").unwrap());
    check_fill_align(IriString::try_from("a:b/c?d#e").unwrap());

    check_fill_align(IriAbsoluteString::try_from("a://b/c?d").unwrap());
    check_fill_align(IriAbsoluteString::try_from("a:///c?d").unwrap());
    check_fill_align(IriAbsoluteString::try_from("a:b/c?d").unwrap());

    check_fill_align(IriRelativeString::try_from("//b/c?d#e").unwrap());
    check_fill_align(IriRelativeString::try_from("///c?d#e").unwrap());
    check_fill_align(IriRelativeString::try_from("b/c?d#e").unwrap());

    check_fill_align(IriFragmentString::try_from("").unwrap());
    check_fill_align(IriFragmentString::try_from("frag").unwrap());

    check_fill_align(IriQueryString::try_from("").unwrap());
    check_fill_align(IriQueryString::try_from("query").unwrap());
    check_fill_align(IriQueryString::try_from("a=b&a=c&d=e").unwrap());

    check_fill_align(UriTemplateString::try_from("").unwrap());
    check_fill_align(UriTemplateString::try_from("a://b/c?d#e").unwrap());
    check_fill_align(
        UriTemplateString::try_from("{scheme}://www{.domain*}{/path*}{?query}{#frag*}").unwrap(),
    );
}
