# Certificate checker performance

The checker retains the same strict ASCII integer grammar and validates every
card, each inside reply, the universal outside class, height descent, ownership,
support containment, White collision, root and graph-depth obligations.

Two repeated costs are reduced:

- Compile the integer-token regular expression once and construct its error
  message only for an invalid token. Arbitrary-size Python integers remain
  supported; signs, leading zeroes and rejection codes keep their semantics.
- Reuse the two transformed child sets for an identical hint within one
  certificate verification, with an LRU limit of 512 entries. Every use still
  checks that hint's reference and height, the parent's ownership/support, and
  the current White reply. The cache stores geometry, never acceptance.
  It is created afresh for each `verify_certificate` call and is released on
  return. The public `check_card` entry point remains an independent check.

The cache trades some temporary allocation for fewer repeated coordinate
transformations. Its entry count is bounded; its byte size depends on the
certificate's point sets. The accompanying benchmark measures that tradeoff.

## Recorded measurements

`checker-performance.json` records five alternating paired trials after warmup
on Windows 10 / Python 3.12.2, against upstream commit
`bc1a91860188a61e73ccca6dd1a6a34082dad59b`, measured on 2026-10-25.
All parsed certificate data and semantic verification fields were identical.

- 19-move certificate: 3,468 cards, 61,040 inside and 3,456 outside checks.
  Median parse-plus-verify time fell from 3.381 s to 2.289 s: **1.48x** speedup,
  approximately 32% less elapsed time. Verification-only traced allocation
  peaked at 1,022,372 bytes before and 4,244,394 bytes after.
- 15x15/24-move certificate: 8,734 cards, 144,288 inside and 8,728 outside
  checks. Median time fell from 9.471 s to 6.435 s: **1.47x** speedup,
  approximately 32% less elapsed time. Verification-only traced allocation
  peaked at 2,476,672 bytes before and 4,740,521 bytes after.

These are measurements on one Windows machine with normal background activity,
not universal speed guarantees. The JSON retains each sample, exact certificate
and checker hashes, Python/platform metadata and memory-measurement scope.
The 512-entry limit was chosen to retain most geometry reuse with less memory
than an initial 4,096-entry probe. No coverage is reduced to obtain the speedup.

## Reproduce

From the repository root with Python 3.10+ and standard-library modules only:

```sh
python3 -m unittest discover -s topics/snaky/verification -p 'test_*.py'
python3 topics/snaky/reproduce.py --baselines
python3 topics/snaky/verification/benchmark_cards.py --baseline bc1a91860188a61e73ccca6dd1a6a34082dad59b --repeats 5 --memory topics/snaky/certificate/snaky19.cards.txt topics/snaky/certificate/snaky15x15-24.cards.txt
```

The benchmark executes the checker from the named trusted Git revision and
the current checker on exactly the same certificate bytes. It compares the
entire parsed data and semantic result, performs an untimed warmup, alternates
which version runs first, and records separate parsing/verification samples.
Explicit garbage collection and result comparisons occur outside timing.
`--memory` adds separate untimed `tracemalloc` measurements of verification
after parsing; these are Python allocation peaks, not process RSS or total
memory including the certificate. Timing has no pass/fail threshold.

The new regression tests exercise a reused hint in a later parent whose
ownership, support or White collision must fail, and a second certificate
whose child changes. They also reject permissive Python integer spellings
such as underscores, a plus sign and non-ASCII digits. Existing terminal,
duplicate-first-response, malformed input, root and transcript controls stay
in place. A checker speedup is not a new strategy, a lower move bound, a new
Lean kernel audit or a proof of optimality.

This performance work and benchmark were prepared with Codex AI assistance.
The game, certificates, mathematical checks and predecessor results retain
their existing authorship and source notices.
