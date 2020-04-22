FROM projecteverest/quackyducky-linux:8ad2426b6751

ADD --chown=everest fstar.sh fstar.sh
ADD --chown=everest init.el .emacs.d/init.el
ADD --chown=everest install-fstar-mode.el install-fstar-mode.el
RUN emacs --script install-fstar-mode.el

ENTRYPOINT ["/bin/bash", "--login"]
