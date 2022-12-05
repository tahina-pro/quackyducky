#!/usr/bin/env bash
# This script builds F* and EverParse, assuming that their build
# dependencies are all installed.
set -e
set -x
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
pwd | grep '/src/package/windows$' > /dev/null
cd ../../..
# This config is necessary if everparse was cloned with non-Cygwin git
git config --global --add safe.directory $(pwd)
# Revert back to a clean working copy
git clean -ffdx
rm -rf FStar karamel hacl-star
git reset HEAD -- .
git checkout .
git submodule update --init
env EVERPARSE_MAKE_OPTS='-j 12' make everparse
