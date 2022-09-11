//! Tests using <https://github.com/uri-templates/uritemplate-test>.

use std::collections::HashMap;
use std::fs::File;
use std::path::Path;

use iri_string::spec::UriSpec;
use iri_string::template::{Context, UriTemplateStr, Value};

use serde::Deserialize;
use serde_json::Value as JsonValue;

#[derive(Debug, Clone, Deserialize)]
struct TestFile {
    #[serde(flatten)]
    tests: HashMap<String, TestSet>,
}

#[derive(Debug, Clone, Deserialize)]
struct TestSet {
    variables: HashMap<String, JsonValue>,
    testcases: Vec<(String, JsonValue)>,
}

fn test_with_file(filename: &str) {
    let base = Path::new("assets/uritemplate-test");
    let path = base.join(Path::new(filename));
    let mut file = File::open(path).expect("test file not found");
    let tests: TestFile = serde_json::from_reader(&mut file).expect("failed to load test asset");

    for (test_set_name, test_set) in &tests.tests {
        let mut context = Context::new();
        for (name, value) in &test_set.variables {
            let value = match value {
                JsonValue::Null => Value::Undefined,
                JsonValue::String(s) => Value::String(s.clone()),
                JsonValue::Array(vec) => {
                    let vec = vec
                        .iter()
                        .map(|v| match v {
                            JsonValue::String(s) => s.clone(),
                            v => panic!("list item of unexpected type: {v:?}"),
                        })
                        .collect();
                    Value::List(vec)
                }
                JsonValue::Object(map) => {
                    let vec = map
                        .iter()
                        .map(|(k, v)| {
                            let v = match v {
                                JsonValue::String(s) => s.clone(),
                                v => panic!("assoc-list item of unexpected type: {v:?}"),
                            };
                            (k.clone(), v)
                        })
                        .collect();
                    Value::Assoc(vec)
                }
                // Note that `arbitrary_precision` flag of `serde_json` crate is expected.
                JsonValue::Number(num) => Value::String(num.to_string()),
                v => panic!("value of unexpected type: {v:?}"),
            };
            context.insert(name, value);
        }

        for (template, expected) in &test_set.testcases {
            let expected = match expected {
                JsonValue::Bool(false) => None,
                JsonValue::String(s) => Some(vec![s.as_str()]),
                JsonValue::Array(arr) => Some(
                    arr.iter()
                        .map(|candidate| {
                            candidate
                                .as_str()
                                .expect("expected strings as result candidates")
                        })
                        .collect::<Vec<_>>(),
                ),
                v => panic!("unexpected `expected` value: {v:?}"),
            };
            let result = UriTemplateStr::new(template)
                .and_then(|template| template.expand::<UriSpec, _>(&context));
            match (result, expected) {
                (Ok(expanded), Some(candidates)) => {
                    let expanded = expanded.to_string();
                    assert!(
                        candidates.contains(&expanded.as_str()),
                        "unexpected expansion result: test={test_set_name:?}, \
                         template={template:?}, expanded={expanded}, candidates={candidates:?}"
                    );
                }
                (Ok(expanded), None) => {
                    panic!(
                        "expected to fail but successfully parsed: test={test_set_name:?},
                         template={template:?}, expanded={expanded}",
                    )
                }
                (Err(e), Some(expected)) => {
                    panic!(
                        "expected to success but failed to parse: {e} \
                         (test={test_set_name:?}, template={template:?}, expected={expected:?})"
                    )
                }
                (Err(_), None) => {}
            }
        }
    }
}

#[test]
fn negative_tests() {
    test_with_file("negative-tests.json");
}

#[test]
fn extended_tests() {
    test_with_file("extended-tests.json");
}

#[test]
fn spec_examples_by_section() {
    test_with_file("spec-examples-by-section.json");
}

#[test]
fn spec_examples() {
    test_with_file("spec-examples.json");
}
