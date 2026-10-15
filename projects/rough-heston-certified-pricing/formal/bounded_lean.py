#!/usr/bin/env python3
"""Serialize this project's Lean checks and cap aggregate process-tree RSS.

Lean's allocator limit can include memory that is not resident. This wrapper
uses the actual resident footprint of only the child process tree it creates.
It never stops or reprioritizes unrelated work.
"""
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

root = Path(__file__).resolve().parent
os.chdir(root)
lock = root / '.compile.lock'
wait_start = time.monotonic()
while True:
    try:
        lock.mkdir()
        break
    except FileExistsError:
        if time.monotonic() - wait_start > 600:
            raise SystemExit('Compile lock still held after 600 seconds; no process was stopped.')
        time.sleep(1)

child = None
peak = 0
status = 1
limit_kib = 2 * 1024 * 1024
env = dict(os.environ)
for name in ('OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS',
             'VECLIB_MAXIMUM_THREADS', 'NUMEXPR_NUM_THREADS'):
    env[name] = '1'
try:
    (lock / 'owner').write_text(str(os.getpid()) + '\n')
    # Resolve the pinned package path first, so Lake is not resident alongside
    # the compiler. No compilation or dependency update occurs in this call.
    env['LEAN_PATH'] = subprocess.check_output(
        ['nice', '-n', '19', 'lake', 'env', 'printenv', 'LEAN_PATH'],
        env=env, text=True).strip()
    command = ['nice', '-n', '19', 'lean', '-j1', *sys.argv[1:]]
    child = subprocess.Popen(command, env=env, start_new_session=True)
    while child.poll() is None:
        rows = subprocess.check_output(['ps', '-axo', 'pid=,ppid=,rss='], text=True)
        processes = [tuple(map(int, line.split())) for line in rows.splitlines() if line.strip()]
        descendants = {child.pid}
        changed = True
        while changed:
            changed = False
            for pid, parent, _ in processes:
                if parent in descendants and pid not in descendants:
                    descendants.add(pid)
                    changed = True
        rss = sum(size for pid, _, size in processes if pid in descendants)
        peak = max(peak, rss)
        if rss > limit_kib:
            print(f'RSS budget exceeded: {rss} KiB > {limit_kib} KiB. Stopping this check only.',
                  file=sys.stderr, flush=True)
            os.killpg(child.pid, signal.SIGTERM)
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
            status = 137
            break
        time.sleep(0.5)
    else:
        status = child.returncode
finally:
    if child is not None and child.poll() is None:
        os.killpg(child.pid, signal.SIGTERM)
        child.wait()
    (lock / 'owner').unlink(missing_ok=True)
    lock.rmdir()
    print(f'Lean check exit={status}; measured peak process-tree RSS={peak} KiB', file=sys.stderr)
raise SystemExit(status)
