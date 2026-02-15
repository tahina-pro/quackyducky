#!/usr/bin/env bash
unset CDPATH
cd "$( dirname "${BASH_SOURCE[0]}" )"
SED=$(which gsed >/dev/null 2>&1 && echo gsed || echo sed)
if [[ "$EVERPARSE_USE_OPAMSWITCH" = 1 ]] ; then
    root_opam="--switch=$OPAMSWITCH"
    set_root=--set-switch
else
    if ! [[ "$EVERPARSE_USE_OPAMROOT" = 1 ]] ; then
        OPAMROOT="$(pwd)/opam"
    elif [[ -z "$OPAMROOT" ]] ; then
	OPAMROOT="$(opam var root | $SED 's!\r!!g')"
    fi
    if [[ "$OS" = Windows_NT ]] ; then
	OPAMROOT="$(cygpath -m "$OPAMROOT")"
    fi
    root_opam="--root=$OPAMROOT"
    set_root=--set-root
    OPAMSWITCH="$OPAMROOT/$(opam switch "$root_opam" show | $SED 's!\r!!g')"
fi
if [[ "$OS" = Windows_NT ]] ; then
    OPAMSWITCH="$(cygpath -m "$OPAMSWITCH")"
fi
opam env "$root_opam" $set_root --shell=sh | grep -v '^PATH=' |
    if [[ "$1" = --shell ]] ; then
	cat
    else
	$SED 's!^\([^=]*\)='"'"'\(.*\)'"'"'; export [^;]*;$!export \1 := \2!'
    fi
if [[ "$1" = --shell ]] ; then
    equal="='"
    epath="'"':"$PATH"'
    eocamlpath=";'"'"$OCAMLPATH"'
else
    equal=':='
    epath=':$(PATH)'
    eocamlpath=';$(OCAMLPATH)'
fi
if [[ "$OS" = Windows_NT ]] ; then
    # Work around an opam bug about `opam var lib`
    echo 'export OCAMLPATH'$equal"$OPAMSWITCH/lib$eocamlpath"
    # convert back because I need Unix-style PATH
    OPAMSWITCH="$(cygpath -u "$OPAMSWITCH")"
fi
echo 'export PATH'$equal"$OPAMSWITCH/bin$epath"
