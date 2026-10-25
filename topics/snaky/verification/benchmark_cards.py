"""Compare this checker with a pinned Git baseline on unchanged certificates.

Run from the repository root. Timings include parsing and complete verification;
result comparisons and optional tracemalloc runs are outside timed samples.
"""
from __future__ import annotations

import argparse
from dataclasses import asdict
import gc
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import tempfile
import time
import tracemalloc


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
CHECKER = "topics/snaky/verification/verify_cards.py"


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def sample(module, text):
    started = time.perf_counter()
    certificate = module.parse_text(text)
    parsed = time.perf_counter()
    result = module.verify_certificate(certificate)
    checked = time.perf_counter()
    return result, {"parse_seconds": parsed - started,
                    "verify_seconds": checked - parsed,
                    "total_seconds": checked - started}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", required=True, help="trusted Git revision to execute")
    parser.add_argument("--repeats", type=int, default=5)
    parser.add_argument("--memory", action="store_true",
                        help="also measure a separate, untimed tracemalloc verification")
    parser.add_argument("certificates", nargs="+", type=Path)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error("--repeats must be positive")
    pin = subprocess.check_output(["git", "rev-parse", "--verify", args.baseline + "^{commit}"],
                                  cwd=ROOT, text=True).strip()
    baseline = subprocess.check_output(["git", "show", pin + ":" + CHECKER], cwd=ROOT)
    output = {"baseline_commit": pin, "baseline_sha256": hashlib.sha256(baseline).hexdigest(),
              "optimized_sha256": hashlib.sha256((ROOT / CHECKER).read_bytes()).hexdigest(),
              "python": platform.python_version(), "platform": platform.platform(),
              "order": "alternating baseline-first and optimized-first after warmup",
              "cache_limit_entries": 512, "certificates": []}
    with tempfile.TemporaryDirectory(prefix="snaky-checker-benchmark-") as directory:
        path = Path(directory) / "baseline.py"
        path.write_bytes(baseline)
        modules = {"baseline": load_module("snaky_baseline", path),
                   "optimized": load_module("snaky_optimized", ROOT / CHECKER)}
        for certificate_path in args.certificates:
            print(f"Comparing {certificate_path}", file=sys.stderr, flush=True)
            data = certificate_path.read_bytes()
            text = data.decode("ascii")
            parsed = {name: module.parse_text(text) for name, module in modules.items()}
            if asdict(parsed["baseline"]) != asdict(parsed["optimized"]):
                raise SystemExit("FAIL: parsed certificate differs")
            reference = modules["baseline"].verify_certificate(parsed["baseline"])
            if modules["optimized"].verify_certificate(parsed["optimized"]) != reference:
                raise SystemExit("FAIL: verification result differs")
            del parsed
            samples = {name: [] for name in modules}
            for repeat in range(args.repeats):
                print(f"  timed pair {repeat + 1}/{args.repeats}", file=sys.stderr, flush=True)
                order = list(modules) if repeat % 2 == 0 else list(reversed(modules))
                for name in order:
                    gc.collect()
                    result, timing = sample(modules[name], text)
                    if result != reference:
                        raise SystemExit("FAIL: timed verification result differs")
                    samples[name].append(timing)
            medians = {name: statistics.median(s["total_seconds"] for s in timings)
                       for name, timings in samples.items()}
            entry = {"path": str(certificate_path),
                     "sha256": hashlib.sha256(data).hexdigest(),
                     "cards": reference["cards_checked"],
                     "inside_checks": reference["inside_reply_checks"],
                     "outside_checks": reference["outside_reply_checks"],
                     "identical_parsing_and_result": True, "samples": samples,
                     "median_seconds": medians,
                     "median_speedup": medians["baseline"] / medians["optimized"]}
            if args.memory:
                peaks = {}
                for name, module in modules.items():
                    print(f"  separate memory run: {name}", file=sys.stderr, flush=True)
                    certificate = module.parse_text(text)
                    gc.collect()
                    tracemalloc.start()
                    result = module.verify_certificate(certificate)
                    _, peaks[name] = tracemalloc.get_traced_memory()
                    tracemalloc.stop()
                    if result != reference:
                        raise SystemExit("FAIL: memory-run verification differs")
                    del certificate
                entry["verification_peak_traced_bytes"] = peaks
            output["certificates"].append(entry)
    print(json.dumps(output, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
