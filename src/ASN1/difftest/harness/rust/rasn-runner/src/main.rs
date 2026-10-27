//! rasn runner for the ASN.1 DER differential tests; see difftest-common.
//! Types are generated from ../../../schemas/*.asn by build.rs.

#![allow(clippy::all, non_camel_case_types, non_snake_case, unused)]
mod generated {
    include!(concat!(env!("OUT_DIR"), "/generated.rs"));
}

use difftest_common::Outcome;
use generated::*;

fn run<T: rasn::Decode>(data: &[u8]) -> Outcome {
    match rasn::der::decode_with_remainder::<T>(data) {
        Ok((_, rem)) => Outcome::Consumed(data.len() - rem.len()),
        Err(e) => Outcome::Reject(e.to_string()),
    }
}

fn decode(ty: &str, data: &[u8]) -> Outcome {
    match ty {
        "DiffSmoke.Smoke" => run::<diff_smoke::Smoke>(data),
        _ => Outcome::Unsupported,
    }
}

fn main() {
    difftest_common::main("rasn", decode)
}
