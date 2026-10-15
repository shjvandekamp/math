#!/bin/sh
# Verify both main theorems, with one compiler process at a time.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
case "${1:-}" in
  ''|--clean) ;;
  *) printf '%s\n' 'Usage: ./verify.sh [--clean]' >&2; exit 2 ;;
esac
./verify-finite.sh "$@"
./verify-structural.sh
printf '%s\n' 'Both finite-basis and arbitrary-period dimension source checks completed.'
