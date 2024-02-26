# This Dockerfile should be run from the root Karamel directory

ARG FSTAR_BRANCH=master
FROM fstar:local-branch-$FSTAR_BRANCH

ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# Dependencies (opam packages)
ENV KRML_HOME=$HOME/everparse/karamel
ENV STEEL_HOME=$HOME/everparse/steel
RUN sudo apt-get update && eval $(opam env) && .docker/build/install-other-deps.sh

# CI dependencies: sphinx (for the docs)
# sudo pip3 because of https://bugs.launchpad.net/ubuntu/+source/bash/+bug/1588562
# jinja2==3.0.0 because of https://github.com/mkdocs/mkdocs/issues/2799
# alabaster==0.7.13 because of https://alabaster.readthedocs.io/en/latest/changelog.html (0.7.14 breaks old Sphinx versions.)
RUN sudo apt-get install --yes --no-install-recommends python3-pip python3-setuptools python3-distutils
RUN sudo pip3 install sphinx==1.7.2 jinja2==3.0.0 alabaster==0.7.13 sphinx_rtd_theme

# CI proper
ARG CI_THREADS=24
ARG CI_BRANCH=master
RUN --mount=type=secret,id=DZOMO_GITHUB_TOKEN eval $(opam env) && DZOMO_GITHUB_TOKEN=$(sudo cat /run/secrets/DZOMO_GITHUB_TOKEN) .docker/build/build-hierarchic.sh $CI_THREADS $CI_BRANCH

WORKDIR $HOME
ENV EVERPARSE_HOME $HOME/everparse
