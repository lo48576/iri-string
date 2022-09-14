use criterion::{criterion_group, criterion_main, Criterion};

use iri_string::types::IriReferenceStr;

pub fn criterion_benchmark(c: &mut Criterion) {
    let domain = "scheme://sub.sub.sub.example.com:8080/a/b/c";
    let v4 = "scheme://198.51.100.23:8080/a/b/c";
    let v6 = "scheme://[2001:db8:0123::cafe]:8080/a/b/c";
    let v6v4 = "scheme://[2001:db8::198.51.100.23]:8080/a/b/c";
    let vfuture = "scheme://[v2.ipv2-does-not-exist]:8080/a/b/c";

    c.bench_function("parse various hosts", |b| {
        b.iter(|| {
            (
                IriReferenceStr::new(domain),
                IriReferenceStr::new(v4),
                IriReferenceStr::new(v6),
                IriReferenceStr::new(v6v4),
                IriReferenceStr::new(vfuture),
            )
        })
    });

    c.bench_function("parse complex path", |b| {
        b.iter(|| {
            let s = concat!(
                "scheme://user:pw@sub.example.com:8080/a/b/c/%30/%31/%32%33%34",
                "/foo/foo/../../../foo.foo/foo/foo/././././//////foo",
                "/\u{03B1}\u{03B2}\u{03B3}/\u{03B1}\u{03B2}\u{03B3}/\u{03B1}\u{03B2}\u{03B3}",
                "?k1=v1&k2=v2&k3=v3#fragment"
            );
            IriReferenceStr::new(s)
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
