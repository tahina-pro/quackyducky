#!/usr/bin/env python3
"""asn1tools runner for the ASN.1 DER differential tests.

Usage: runner.py SCHEMA_DIR MANIFEST RESULTS

Compiles every SCHEMA_DIR/*.asn module separately with the 'der' codec, then
decodes each manifest vector ("type" is "Module.Type") and writes one JSON
object per line to RESULTS: {id, impl, verdict, consumed[, error]}.
The verdict is "accept" iff decoding succeeds and consumes the whole input;
"unsupported" if the module does not compile or lacks the type; "error" if
the decoder raised something other than an asn1tools error (a crash).
"""

import glob
import json
import os
import sys

import asn1tools


def compile_modules(schema_dir):
    specs = {}
    for path in sorted(glob.glob(os.path.join(schema_dir, '*.asn'))):
        try:
            spec = asn1tools.compile_files([path], 'der')
        except Exception as e:  # unsupported construct
            print(f'asn1tools: cannot compile {path}: {e}', file=sys.stderr)
            continue
        for module in spec.modules:
            specs[module] = spec
    return specs


def run_vector(specs, v):
    module, _, ty = v['type'].partition('.')
    spec = specs.get(module)
    if spec is None or ty not in spec.types:
        return {'verdict': 'unsupported', 'consumed': None}
    data = bytes.fromhex(v['hex'])
    try:
        _, n = spec.decode_with_length(ty, data)
    except asn1tools.Error as e:
        return {'verdict': 'reject', 'consumed': None, 'error': str(e)}
    except Exception as e:
        return {'verdict': 'error', 'consumed': None,
                'error': f'{type(e).__name__}: {e}'}
    return {'verdict': 'accept' if n == len(data) else 'reject',
            'consumed': n}


def main():
    schema_dir, manifest, results = sys.argv[1:4]
    specs = compile_modules(schema_dir)
    with open(manifest) as f:
        vectors = json.load(f)['vectors']
    with open(results, 'w') as out:
        for v in vectors:
            r = {'id': v['id'], 'impl': 'asn1tools'}
            r.update(run_vector(specs, v))
            out.write(json.dumps(r) + '\n')


if __name__ == '__main__':
    main()
