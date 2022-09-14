use criterion::{criterion_group, criterion_main, Criterion};

use core::fmt::Write;

use iri_string::format::{write_to_slice, ToDedicatedString};
use iri_string::resolve::FixedBaseResolver;
use iri_string::types::{IriAbsoluteStr, IriReferenceStr};

pub fn criterion_benchmark(c: &mut Criterion) {
    let base = IriAbsoluteStr::new("https://sub.example.com/foo1/foo2/foo3/foo4/foo5")
        .expect("should be valid IRI");
    let rel = IriReferenceStr::new(concat!(
        "bar1/bar2/bar3/../bar4/../../bar5/bar6/bar7/../../../../..",
        "/bar8/../../../bar9/././././././bar10/bar11",
    ))
    .expect("should be valid IRI");

    c.bench_function("resolve (new task, new buf)", |b| {
        b.iter(|| rel.resolve_against(base).to_dedicated_string())
    });

    c.bench_function("resolve (task reuse, new buf)", |b| {
        let task = FixedBaseResolver::new(base).resolve(rel);
        b.iter(|| task.to_dedicated_string());
    });

    c.bench_function("resolve (task reuse, buf reuse)", |b| {
        let mut buf = String::new();
        let task = FixedBaseResolver::new(base).resolve(rel);
        b.iter(|| {
            buf.clear();
            write!(&mut buf, "{}", task).expect("write to `String` should never fail");
        });
    });

    c.bench_function("resolve (task reuse, fixed buf reuse)", |b| {
        let mut buf = [0_u8; 512];
        let task = FixedBaseResolver::new(base).resolve(rel);
        b.iter(move || {
            write_to_slice(&mut buf, &task).expect("`buf` should have enough capacity");
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
