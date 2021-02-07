#!/bin/sh
# bootstrap script

(
alias redo-ifchange=:
set -- redo redo redo
set -ex
. ./redo.do
)

export PATH=$PWD:$PATH
redo -f links
redo -f all
