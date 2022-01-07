#![feature(bench_black_box)]

use iri_string::resolve::resolve;
use iri_string::types::{IriAbsoluteStr, IriReferenceStr};

fn main() {
    let base = IriAbsoluteStr::new("https://sub.example.com/foo1/foo2/foo3/foo4/foo5")
        .expect("should be valid IRI");
    let rel = IriReferenceStr::new(
        "bar1/bar2/bar3/../bar4/../../bar5/../../../../../bar6/../../../bar7/././././././bar8/bar9",
    )
    .expect("should be valid IRI");
    for _ in 0..100000 {
        let resolved = resolve(rel, base);
        drop(std::hint::black_box(resolved));
    }
}
