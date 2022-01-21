#!/usr/bin/env bash
# This script builds F* and EverParse, assuming that their build
# dependencies are all installed.
set -e
set -x
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
pwd | grep '/src/package/windows$' > /dev/null
cd ../../..
rm -rf everparse
make everparse
