#!/bin/sh
# Check the general source-family foundations; this does not prove independence.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
if [ -n "${LEAN_BIN:-}" ]; then
  PATH="$LEAN_BIN:$PATH"
  export PATH
fi
command -v lake >/dev/null 2>&1 || {
  printf '%s\n' 'Install the pinned Lean toolchain or set LEAN_BIN to its bin directory.' >&2
  exit 127
}
case "${1:-}" in
  '') clean_outputs=false ;;
  --clean) clean_outputs=true ;;
  *) printf '%s\n' 'Usage: ./verify-source-family.sh [--clean]' >&2; exit 2 ;;
esac
export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1
proof_memory_mb="${LEAN_MEMORY_MB:-2500}"
case "$proof_memory_mb" in
  ''|*[!0-9]*) printf '%s\n' 'LEAN_MEMORY_MB must be a positive integer.' >&2; exit 2 ;;
esac
[ "$proof_memory_mb" -gt 0 ]

verification_tmp=$(mktemp -d "${TMPDIR:-/tmp}/panel-moments-source-family.XXXXXX")
trap 'rm -rf "$verification_tmp"' EXIT HUP INT TERM
cd formal
lean_executable=$(command -v lean)
[ "$("$lean_executable" --short-version)" = '4.34.1' ] || {
  printf '%s\n' 'This artifact requires Lean 4.34.1.' >&2
  exit 1
}
python3 - <<'PY'
import json
import pathlib
import subprocess

manifest = json.loads(pathlib.Path("lake-manifest.json").read_text())
for package in manifest["packages"]:
    checkout = pathlib.Path(manifest["packagesDir"]) / package["name"]
    actual = subprocess.check_output(["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True).strip()
    if actual != package["rev"]:
        raise SystemExit(f"Dependency revision mismatch: {package['name']}")
    subprocess.run(["git", "-C", str(checkout), "diff", "--quiet", "HEAD", "--"], check=True)
PY
# Lake resolves the environment, then exits before any compiler starts.
LEAN_PATH=$(lake env printenv LEAN_PATH)
export LEAN_PATH
source_modules='Model Polynomial SourceMoments BasisCertificate PermutationMoments MomentLifts SourceFamily SourceCounting PermutationLifts SourceRecursion SourceLifts SourceNewIndices SourceConditional SourceJointImage SourceTransfer KernelProducts SourceTransferOrders SourceSingleBlock SourceReducedCriterion SourceHomogeneous SourceHomogeneousCriterion SourcePolynomialKernels SourceCoordinateFactors SourcePolynomialCriterion BinaryTransferAlgebra BinaryTransferSpan BinaryTransferEndpoints BinaryTransferIndependence BinaryTransferRank BinaryTransferMatrices BinaryTransferPositiveRank'
if [ "$clean_outputs" = true ]; then
  for module_name in $source_modules; do
    output_path=".lake/build/lib/lean/PanelMoments/$module_name"
    rm -f "$output_path.olean" "$output_path.olean.private" \
      "$output_path.olean.server" "$output_path.ilean"
  done
fi
for module_name in $source_modules; do
  output_path=".lake/build/lib/lean/PanelMoments/$module_name"
  mkdir -p "$(dirname -- "$output_path")"
  printf 'Checking PanelMoments.%s\n' "$module_name"
  nice -n 19 "$lean_executable" -M "$proof_memory_mb" -j 1 \
    "PanelMoments/$module_name.lean" -o "$output_path.olean" -i "$output_path.ilean"
done
nice -n 19 "$lean_executable" -M "$proof_memory_mb" -j 1 \
  SourceFamilyCheck.lean > "$verification_tmp/axioms"
cat "$verification_tmp/axioms"
python3 - "$verification_tmp/axioms" <<'PY'
import pathlib
import re
import sys

audit = pathlib.Path(sys.argv[1]).read_text()
results = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit))
results.update((name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", audit))
requested = set(re.findall(r"^#print axioms (\S+)", pathlib.Path("SourceFamilyCheck.lean").read_text(), re.M))
if requested - results.keys():
    raise SystemExit(f"Incomplete axiom output: {sorted(requested - results.keys())}")
allowed = {"propext", "Classical.choice", "Quot.sound"}
for group in results.values():
    actual = {item.strip() for item in group.split(",") if item.strip()}
    if actual - allowed:
        raise SystemExit(f"Unexpected axioms: {sorted(actual - allowed)}")
for path in pathlib.Path("PanelMoments").rglob("*.lean"):
    text = path.read_text()
    if re.search(r"\b(?:sorry|admit|sorryAx|native_decide)\b|\+native|^\s*axiom\b", text, re.M):
        raise SystemExit(f"Forbidden proof construct in {path}")
print(f"{len(requested)} source-family foundation declarations use only permitted foundational axioms.")
PY
cp "$verification_tmp/axioms" source-family-axioms.txt
printf '%s\n' 'Serial source-family foundation verification completed; arbitrary-T independence is not asserted.'
