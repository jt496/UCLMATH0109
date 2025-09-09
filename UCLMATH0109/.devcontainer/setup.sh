#!/usr/bin/env bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \
  | sh -s -- --default-toolchain none  -y # Install the elan Lean version manager
export PATH=$PATH:~/.elan/bin
lake exe cache get!