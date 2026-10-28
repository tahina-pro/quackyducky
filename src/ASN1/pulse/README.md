# Verified C validators for ASN.1 DER (Pulse + Custard)

This directory implements, in Pulse, validators for the pure F\* ASN.1 DER
specification of `..` (`ASN1.Spec.Interpreter`), and extracts them to C
with Custard (F\*'s direct-to-C backend; no KaRaMeL).

A validator for a schema `k` checks that a byte buffer starts with a value
of `asn1_as_parser k` and returns the number of bytes consumed; it is
proven to succeed exactly when the spec parser succeeds, with the same
consumed length (`LowParse.Pulse.Base.validator`).

## Coverage

Every schema construct of the specification: all universal terminal types,
restricted terminals (`asn1_restriction`), PREFIXED (EXPLICIT tags),
SEQUENCE (OPTIONAL, DEFAULT for BOOLEAN and NULL), SEQUENCE OF, SET OF
(DER ordering), SET (at most 64 components), CHOICE, ANY, ANY DEFINED BY
(OBJECT IDENTIFIER keys, with or without a prefix, with or without a
fallback), and the presentation types (EXTERNAL, EMBEDDED PDV, CHARACTER
STRING). The interpreter rejects unsupported schemas statically
(`supported_k`), which the extraction roots discharge by normalization.

## Layout

| Module | Contents |
| --- | --- |
| `ASN1.Pulse.Identifier`, `ASN1.Pulse.ILC` | identifier and length readers, TLV framing |
| `ASN1.Pulse.Terminal`, `ASN1.Pulse.Checkers`, `ASN1.Pulse.OID` | terminal contents |
| `ASN1.Pulse.Restrict` | restricted terminals |
| `ASN1.Pulse.Sequence`, `ASN1.Pulse.SeqAny` | SEQUENCE items, and the prefix of ANY DEFINED BY |
| `ASN1.Pulse.Constructed`, `ASN1.Pulse.SetOf`, `ASN1.Pulse.SetComp` | SEQUENCE OF, CHOICE, SET OF, SET |
| `ASN1.Pulse.Any`, `ASN1.Pulse.AnyDefinedBy` | ANY, ANY DEFINED BY |
| `ASN1.Pulse.Interpreter` | the interpreter `validate_k` over schemas |
| `ASN1.Pulse.DiffTest.*` | extraction roots for the difftest schemas (`../difftest`) |
| `ASN1.Pulse.X509` | extraction roots for X.509 certificates and CRLs |

Generic parts live in LowParse (`lib/everparse/lowparse`), e.g.
`LowParse.PulseParse.VReader` (validate-and-read combinators) and
`LowParse.Pulse.Lex` (lexicographic comparison, for SET OF).

## Code shape

* **One C function per schema node.** The interpreter is not inlined:
  its schema arguments carry `[@@@FStar.Attributes.monomorphize]`, so
  Custard emits one specialization of each interpreter function per
  distinct schema value it is applied to (identical sub-schemas share one
  C function).
* **Bounded stack.** No C function is recursive; the call depth is bounded
  by the depth of the schema. ANY values, whose nesting depth is
  controlled by the input, are validated by a loop with constant stack
  (`ASN1.Pulse.Any`, `validate_rec_vlgen`). No heap allocation.
* Extraction roots are plain F\* `let`s with `normalize_for_extraction`
  (see `ASN1.Pulse.X509`), unfolding the schema definitions.

Custard pitfalls met in this code (comments in `ASN1.Pulse.Interpreter`):

* Custard F\* 4cb038ec6f misclassifies the binders that a specialized
  function gets from the lambdas of its body (wrong parameters are
  dropped), so every monomorphized validator takes the validator arguments
  explicitly and returns `vres ...`.
* In a specialization, `let C x = v` and `match v with C x -> ...` on a
  monomorphized value do not reduce: use projectors (`C?.x v`).
* A monomorphized argument must not be a closure whose type mentions the
  schema (Error 368): rebuild the closure in the callee instead.

## Build and test

```
make            # verify
make test       # difftest vectors (committed verdicts)
make test-oracle  # difftest vectors and mutations, against the F* spec runner
make test-corpus  # X.509 and CRL corpora (../evaluation/data), against the spec runner
make test-deep-any  # ANY nested 4000 deep, under a 64 KiB stack limit
make stack-check    # no recursion, and worst-case stack of the X.509/CRL validators
```

`make -C .. test` runs all of these, unless `NO_PULSE` is set. C files
go to `_output/`.

Reference numbers (one core, x86-64): extracting `ASN1.Pulse.X509`
(certificates and CRLs) takes about 5 minutes and yields 959 KB of C
(62 KB of code at -O1); the X.509 corpus (14620 files) and the CRL
corpus (6154 files) agree with the spec runner on every file; the
worst-case stack is 16 KB at -O0 (4 KB at -O1) for a certificate;
validating the whole X.509 corpus (14.6 MB) takes about 0.1 s, file I/O
included.
