#!/bin/bash
set -euo pipefail

project_dir="$(cd "$(dirname "$0")" && pwd)"
cd "$project_dir/formal"

# Prefer the already-installed pinned runtime on this machine. On another
# machine, elan may provide the version fixed by lean-toolchain instead.
pinned_bin=/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin
if [ -x "$pinned_bin/lean" ]; then
  export PATH="$pinned_bin:$PATH"
fi
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
export VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1

lean --version | tee "$project_dir/certificates/toolchain.txt"
lean --version | head -1 | grep -q 'version 4.34.1'

if [ ! -f .lake/packages/mathlib/Mathlib.lean ]; then
  nice -n 19 lake update
  nice -n 19 lake exe cache get
fi
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = d13f23b723b8a846827a245b89c10fc7d3f11612

# Reject proof holes and unchecked native-computation tactics in project
# sources. Kernel axiom output below is the stronger dependency check.
python3 - <<'PY'
from pathlib import Path
import re
bad = re.compile(r'\b(sorry|admit|sorryAx|axiom|native_decide|unsafe)\b')
for path in [Path('RoughHeston.lean'), *Path('RoughHeston').glob('*.lean')]:
    # Remove comments before scanning; AxiomAudit's #print axioms is permitted.
    text = re.sub(r'/\-.*?\-/', '', path.read_text(), flags=re.S)
    text = re.sub(r'--[^\n]*', '', text)
    if bad.search(text):
        raise SystemExit(f'Forbidden proof construct in {path}')
PY

# Clear only this project's generated Lean outputs. Dependencies are pinned
# and cached; no unrelated checkout or process is modified.
python3 - <<'PY'
from pathlib import Path
import shutil
for folder in (Path('.lake/build/lib/lean/RoughHeston'),):
    if folder.exists():
        shutil.rmtree(folder)
    folder.mkdir(parents=True)
for path in Path('.lake/build/lib/lean').glob('RoughHeston.*'):
    if path.is_file():
        path.unlink()
PY

build_log="$project_dir/certificates/clean-build.log"
: > "$build_log"
# Derive the local dependency order from the public library entrypoint,
# so adding a headline module cannot silently omit its supporting proofs.
python3 - <<'PY'
from pathlib import Path
import re
done, active, ordered = set(), set(), []
def visit(name):
    if name in done:
        return
    if name in active:
        raise SystemExit(f'Local import cycle: {name}')
    active.add(name)
    path = Path(name.replace('.', '/') + '.lean')
    for dependency in re.findall(r'^(?:public )?import (RoughHeston(?:\.[\w]+)*)\s*$',
                                 path.read_text(), re.M):
        visit(dependency)
    active.remove(name)
    done.add(name)
    ordered.append(name.replace('.', '/'))
visit('RoughHeston')
Path('.lake/build/project-modules.txt').write_text('\n'.join(ordered) + '\n')
PY
while IFS= read -r module; do
  python3 bounded_lean.py -o ".lake/build/lib/lean/$module.olean" \
    "$module.lean" 2>&1 | tee -a "$build_log"
done < .lake/build/project-modules.txt
python3 bounded_lean.py RoughHeston/AxiomAudit.lean 2>&1 \
  | tee "$project_dir/certificates/axioms.txt"
if grep -q 'sorryAx' "$project_dir/certificates/axioms.txt"; then
  exit 1
fi
printf 'Clean verification exit status: 0\n' | tee -a "$build_log"
