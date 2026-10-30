#!/bin/sh
set -eu

cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if [ -n "${LEAN_BIN:-}" ]; then
  PATH="$LEAN_BIN:$PATH"
  export PATH
fi
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'lake is unavailable; install the pinned toolchain or set LEAN_BIN to its bin directory.' >&2
  exit 127
fi
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1
proof_memory_mb="${LEAN_MEMORY_MB:-2350}"
case "$proof_memory_mb" in
  ''|*[!0-9]*) printf '%s\n' 'LEAN_MEMORY_MB must be a positive integer.' >&2; exit 2 ;;
esac
[ "$proof_memory_mb" -gt 0 ]
LEAN_PATH=$(lake env printenv LEAN_PATH)
export LEAN_PATH
mkdir -p .lake/build/lib/lean/PanelMoments
for module_name in Model Polynomial Economic Degree; do
  nice -n 19 lean -M "$proof_memory_mb" -j 1 "PanelMoments/$module_name.lean" \
    -o ".lake/build/lib/lean/PanelMoments/$module_name.olean" \
    -i ".lake/build/lib/lean/PanelMoments/$module_name.ilean"
done
nice -n 19 lean -M "$proof_memory_mb" -j 1 FoundationCheck.lean
