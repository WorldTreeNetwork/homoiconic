#!/bin/sh
# Check the spike language, run both routes on every scenario, and check the two reduction proofs.
set -eu
cd "$(dirname "$0")"
export PATH="$HOME/.elan/bin:$PATH"
lean src/Spike.lean
