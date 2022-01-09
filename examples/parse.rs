//! An example to parse IRI from the CLI argument.

use iri_string::types::RiReferenceStr;

const USAGE: &str = "\
USAGE:
    parse [FLAGS] [--] IRI

FLAGS:
    -h, --help      Prints this help
    -i, --iri       Handle the input as an IRI (RFC 3987)
    -u, --uri       Handle the input as an URI (RFC 3986)

ARGS:
    <IRI>           IRI or URI
";

fn print_help() {
    eprintln!("{}", USAGE);
}

fn help_and_exit() -> ! {
    print_help();
    std::process::exit(1);
}

fn die(msg: impl std::fmt::Display) -> ! {
    eprintln!("ERROR: {}", msg);
    eprintln!();
    print_help();
    std::process::exit(1);
}

/// Syntax specification.
#[derive(Debug, Clone, Copy)]
enum Spec {
    /// RFC 3986 URI.
    Uri,
    /// RFC 3987 IRI.
    Iri,
}

impl Default for Spec {
    #[inline]
    fn default() -> Self {
        Self::Iri
    }
}

/// CLI options.
#[derive(Default, Debug, Clone)]
struct CliOpt {
    /// IRI.
    iri: String,
    /// Syntax spec.
    spec: Spec,
}

impl CliOpt {
    fn parse() -> Self {
        let mut args = std::env::args();
        // Skip `argv[0]`.
        args.next();

        let mut iri = None;
        let mut spec = None;

        for arg in args.by_ref() {
            match arg.as_str() {
                "--iri" | "-i" => spec = Some(Spec::Iri),
                "--uri" | "-u" => spec = Some(Spec::Uri),
                "--help" | "-h" => help_and_exit(),
                opt if opt.starts_with('-') => die(format_args!("Unknown option: {}", opt)),
                _ => {
                    if iri.replace(arg).is_some() {
                        die("IRI can be specified at most once");
                    }
                }
            }
        }

        for arg in args {
            if iri.replace(arg).is_some() {
                eprintln!("ERROR: IRI can be specified at most once");
            }
        }

        let iri = iri.unwrap_or_else(|| die("IRI should be specified"));
        let spec = spec.unwrap_or_default();
        Self { iri, spec }
    }
}

fn main() {
    let opt = CliOpt::parse();

    match opt.spec {
        Spec::Iri => parse::<iri_string::spec::IriSpec>(&opt),
        Spec::Uri => parse::<iri_string::spec::UriSpec>(&opt),
    }
}

fn parse<S: iri_string::spec::Spec>(opt: &CliOpt) {
    let raw = &opt.iri.as_str();
    let iri = match RiReferenceStr::<S>::new(raw) {
        Ok(v) => v,
        Err(e) => die(format_args!("Failed to parse {:?}: {}", raw, e)),
    };
    println!("Successfully parsed: {:?}", iri);

    match iri.to_iri() {
        Ok(iri) => {
            println!("IRI is ablolute.");
            match iri.fragment() {
                Some(frag) => println!("IRI has a fragment: {:?}.", frag),
                None => println!("IRI has no fragment."),
            }
        }
        Err(_) => println!("IRI is relative."),
    }
}
