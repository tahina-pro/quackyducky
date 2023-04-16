# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# CI dependencies: jq (to identify F* branch)
RUN sudo apt-get update && sudo apt-get install -y --no-install-recommends jq

# Dependencies (F*, Karamel and opam packages)
ENV FSTAR_HOME=$HOME/FStar
ENV KRML_HOME=$HOME/karamel
ENV FSTAR_BRANCH=taramana_no_steel
RUN eval $(opam env) && .docker/build/install-deps.sh

ARG CI_THREADS=24

# Steel
ENV STEEL_HOME=$HOME/steel
RUN git clone https://github.com/tahina-pro/steel-draft $STEEL_HOME && \
     eval $(opam env) && env OTHERFLAGS='--admit_smt_queries true' make -j $CI_THREADS -C $STEEL_HOME

# CI proper
ENV STEEL_C=1
RUN eval $(opam env) && make -j $CI_THREADS steel-unit-test cbor

WORKDIR $HOME
ENV EVERPARSE_HOME=$HOME/everparse
