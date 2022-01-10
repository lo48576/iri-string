use criterion::{criterion_group, criterion_main, Criterion};

use iri_string::resolve::FixedBaseResolver;
use iri_string::types::{IriReferenceStr, IriStr};

pub fn criterion_benchmark(c: &mut Criterion) {
    let base = IriStr::new("https://sub.example.com/foo1/foo2/foo3/foo4/foo5")
        .expect("should be valid IRI");
    let rel = IriReferenceStr::new(concat!(
        "bar1/bar2/bar3/../bar4/../../bar5/bar6/bar7/../../../../..",
        "/bar8/../../../bar9/././././././bar10/bar11",
    ))
    .expect("should be valid IRI");

    c.bench_function("resolve (new task, new buf)", |b| {
        b.iter(|| {
            rel.resolve_against(base)
                .expect("resolvable inputs should be passed")
        })
    });

    c.bench_function("resolve (task reuse, new buf)", |b| {
        let task = FixedBaseResolver::new(base).create_task(rel);
        b.iter(|| {
            task.allocate_and_write()
                .expect("resolvable inputs should be passed")
        });
    });

    c.bench_function("resolve (task reuse, buf reuse)", |b| {
        let mut buf = String::new();
        let task = FixedBaseResolver::new(base).create_task(rel);
        b.iter(|| {
            buf.clear();
            task.append_to_std_string(&mut buf)
                .expect("resolvable inputs should be passed");
        });
    });

    c.bench_function("resolve (task reuse, fixed buf reuse)", |b| {
        let mut buf = [0_u8; 512];
        let task = FixedBaseResolver::new(base).create_task(rel);
        b.iter(|| {
            task.write_to_byte_slice(&mut buf)
                .expect("resolvable inputs and long buffer should be passed");
        });
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
