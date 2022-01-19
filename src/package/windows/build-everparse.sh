#!/usr/bin/env bash
# This script builds F* and EverParse, assuming that their build
# dependencies are all installed.
set -e
set -x
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
pwd | grep '/src/package/windows$' > /dev/null
z3_dir=$(dirname $(which z3.exe))
cp $z3_dir/../lib/*.dll $z3_dir || true
touch $z3_dir/z3dummy.lib
rm -rf everparse
make everparse
rm everparse/bin/z3dummy.lib
