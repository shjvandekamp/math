#!/bin/sh
# Recompile the finite main theorem serially; generated certificates are never trusted.
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
  '') ;;
  --clean) rm -rf formal/.lake/build ;;
  *) printf '%s\n' 'Usage: ./verify-finite.sh [--clean]' >&2; exit 2 ;;
esac

export LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1
export MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1
proof_memory_mb="${LEAN_MEMORY_MB:-2500}"
case "$proof_memory_mb" in
  ''|*[!0-9]*) printf '%s\n' 'LEAN_MEMORY_MB must be a positive integer.' >&2; exit 2 ;;
esac
[ "$proof_memory_mb" -gt 0 ]

verification_tmp=$(mktemp -d "${TMPDIR:-/tmp}/panel-moments-verify.XXXXXX")
trap 'rm -rf "$verification_tmp"' EXIT HUP INT TERM
python3 exploration/exact_q3t4.py --output "$verification_tmp/q3t4-certificate.json"
cmp exploration/q3t4-certificate.json "$verification_tmp/q3t4-certificate.json"
python3 exploration/generate_lean_witness.py --check
python3 exploration/generate_lean_witness.py --list-data-modules > "$verification_tmp/data-modules"
python3 exploration/generate_lean_witness.py --list-modules > "$verification_tmp/modules"

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
# Resolve Lake's environment once, then release its process before each compiler.
LEAN_PATH=$(lake env printenv LEAN_PATH)
export LEAN_PATH
compile_module() {
  module_path=$(printf '%s' "$1" | tr . /)
  output_path=".lake/build/lib/lean/$module_path"
  mkdir -p "$(dirname -- "$output_path")"
  printf 'Checking %s\n' "$1"
  nice -n 19 "$lean_executable" -M "$proof_memory_mb" -j 1 \
    "$module_path.lean" -o "$output_path.olean" -i "$output_path.ilean"
}

# Topological order prevents Lake from spawning parallel dependency builds.
for module_name in Model Polynomial Economic Degree Geometry Genericity SourceMoments \
    SourceAnalytic BasisCertificate
do
  compile_module "PanelMoments.$module_name"
done
while IFS= read -r module_name; do
  [ -z "$module_name" ] || compile_module "$module_name"
done < "$verification_tmp/data-modules"
for module_name in WitnessRows WitnessCore SourceRestrictions ModelAnalytic; do
  compile_module "PanelMoments.$module_name"
done
while IFS= read -r module_name; do
  [ -z "$module_name" ] || compile_module "$module_name"
done < "$verification_tmp/modules"
for module_name in Witness FiniteCompleteness EconomicGenericity
do
  compile_module "PanelMoments.$module_name"
done
compile_module PanelMoments

nice -n 19 "$lean_executable" -M "$proof_memory_mb" -j 1 MainCheck.lean > "$verification_tmp/axioms"
cat "$verification_tmp/axioms"
python3 - "$verification_tmp/axioms" <<'PY'
import pathlib
import re
import sys

audit = pathlib.Path(sys.argv[1]).read_text()
results = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", audit))
results.update((name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", audit))
requested = set(re.findall(r"^#print axioms (\S+)", pathlib.Path("MainCheck.lean").read_text(), re.M))
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
print("Main theorem and audited dependencies use only permitted foundational axioms.")
PY
cp "$verification_tmp/axioms" main-axioms.txt
printf '%s\n' 'Serial source verification completed. See VERIFICATION.md for the statement audit and scope.'
