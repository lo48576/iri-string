//! Test cases for issues reported on GitHub.

use iri_string::types::UriReferenceStr;

mod issue_17 {
    use super::*;

    #[test]
    fn ipv6_literal_authority_host() {
        let uri = UriReferenceStr::new("//[::1]").expect("valid relative URI");
        let authority = uri
            .authority_components()
            .expect("the URI has authority `[::1]`");
        assert_eq!(authority.host(), "[::1]");
    }

    #[test]
    fn extra_trailing_colon_in_ipv6_literal() {
        assert!(UriReferenceStr::new("//[::1:]").is_err());
    }

    #[test]
    fn ipvfuture_literal_capital_v() {
        assert!(UriReferenceStr::new("//[v0.0]").is_ok());
        assert!(UriReferenceStr::new("//[V0.0]").is_ok());
    }
}
