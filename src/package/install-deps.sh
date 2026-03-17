#!/bin/bash
set -e
set -x
git submodule init
git submodule update
# Install the Everest OPAM package dependencies
./lib/everparse/opt/everest/everest --yes opam
