# This Dockerfile should be run from the root EverParse directory

ARG ocaml_version=4.12
FROM ocaml/opam:ubuntu-ocaml-$ocaml_version

# Set up git identity
RUN git config --global user.name 'Dzomo, the Everest Yak'
ARG DZOMO_EMAIL
RUN git config --global user.email $DZOMO_EMAIL

# Install GitHub CLI
# From https://github.com/cli/cli/blob/trunk/docs/install_linux.md#debian-ubuntu-linux-raspberry-pi-os-apt
RUN { type -p curl >/dev/null || sudo apt install curl -y ; } \
    && curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg \
    && sudo chmod go+r /usr/share/keyrings/githubcli-archive-keyring.gpg \
    && echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | sudo tee /etc/apt/sources.list.d/github-cli.list > /dev/null \
    && sudo apt update \
    && sudo apt install gh -y

# Bring in the contents
ADD --chown=opam:opam ./ $HOME/everparse/
WORKDIR $HOME/everparse

# Install opam package dependencies
RUN eval $(opam env) && src/package/windows/everest.sh opam

# Build and publish the release
ARG CI_THREADS=24
ARG EVERPARSE_RELEASE_ORG=project-everest
ARG EVERPARSE_RELEASE_REPO=everparse
ARG DZOMO_GITHUB_TOKEN
RUN eval $(opam env) && GH_TOKEN=$DZOMO_GITHUB_TOKEN EVERPARSE_RELEASE_ORG=$EVERPARSE_RELEASE_ORG EVERPARSE_RELEASE_REPO=$EVERPARSE_RELEASE_REPO make -j $CI_THREADS release
