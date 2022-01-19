#!/usr/bin/env bash
# This script builds F* and EverParse, assuming that their build
# dependencies are all installed.
set -e
set -x
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
pwd | grep '/src/package/windows$' > /dev/null
if z3_dir=$(dirname $(which z3.exe)) ; then
    cp $z3_dir/../lib/*.dll $z3_dir || true
    touch $z3_dir/z3dummy.lib
fi
cd ../../..
rm -rf everparse
make everparse
rm -f everparse/bin/z3dummy.lib
