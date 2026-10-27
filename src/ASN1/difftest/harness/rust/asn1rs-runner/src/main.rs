//! asn1-rs runner for the ASN.1 DER differential tests; see difftest-common.
//!
//! asn1-rs has no ASN.1 compiler: every type of ../../../schemas/*.asn
//! is translated by hand below, with the asn1-rs derive macros.

#![allow(dead_code)]
use asn1_rs::*;
use difftest_common::Outcome;

/// Generic driver: parse with `FromDer`, report bytes consumed.
fn run<'a, T: FromDer<'a, asn1_rs::Error>>(data: &'a [u8]) -> Outcome {
    match T::from_der(data) {
        Ok((rem, _)) => Outcome::Consumed(data.len() - rem.len()),
        Err(e) => Outcome::Reject(e.to_string()),
    }
}

mod diff_smoke {
    use asn1_rs::*;

    // Smoke ::= SEQUENCE { a INTEGER, b BOOLEAN OPTIONAL, c OCTET STRING }
    #[derive(Debug, DerSequence)]
    pub struct Smoke<'a> {
        pub a: Integer<'a>,
        #[optional]
        pub b: Option<bool>,
        pub c: OctetString<'a>,
    }
}

fn decode(ty: &str, data: &[u8]) -> Outcome {
    match ty {
        "DiffSmoke.Smoke" => run::<diff_smoke::Smoke>(data),
        _ => Outcome::Unsupported,
    }
}

fn main() {
    difftest_common::main("asn1-rs", decode)
}
