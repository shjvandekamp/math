# Independent compact-card audit

`verify_cards.py` uses only the Python standard library. It reads the compact
`snaky-cards-txt-v1` interface and checks the mathematical conditions directly.
It does not import the source repository's checker, constructors, or search
helpers. No strategy search occurs here.

See [performance measurements and reproduction](PERFORMANCE.md) for the
bounded geometry cache, strict-parser optimization and baseline comparison.

Run from the repository root:

```sh
python3 -m unittest discover -s topics/snaky/verification -p 'test_*.py' -v
python3 topics/snaky/verification/verify_cards.py /path/to/cards-17x17.txt --json
```

For a proposed nineteen-move certificate, add `--max-root-height 19`. This flag
requires the **declared** root height to meet the bound; it does not silently
change a certificate's heights or choose alternative hints.

## Meaning of an accepted certificate

The game is the finite-board maker-breaker game: Black moves first, both players
place one stone on an unoccupied cell, and Black wins on owning all six cells of
a translated rotation or reflection of
`{(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}`. The height counts Black's moves, including
the final winning move. It does not count plies, and it does not assert an exact
or optimal winning time.

For a card `(A,S,p,h)`, `A` is required Black ownership; `S` is a set containing
no White stone; `p` is the next pivot; and `h` is a positive upper bound. `S`
can overlap `A`, and need not contain all of `A`. Extra Black stones are allowed.
The verifier checks these obligations:

1. The pivot is in `S` and the height is positive.
2. Either `A ∪ {p}` contains an exact six-cell D4 Snaky placement, or all the
   following response obligations hold.
3. Every point `w` in `S \ (A ∪ {p})` has a hint. Its child has smaller positive
   height; its transform is a genuine D4 symmetry followed by an integer
   translation; its transformed requirements lie in `A ∪ {p}`; and its
   transformed support lies in `S \ {w}`.
4. An outside-support hint satisfies the same requirements with child support
   contained in `S`. It covers **every** legal White move outside `S`, including
   holes inside the bounding rectangle and all cells beyond that rectangle.
   Enumerating a large finite bounding box would not establish this obligation.
5. The named root has no Black requirements, its transformed support fits on
   the stated board, and `2h ≤ rows × columns`.

The resulting induction uses the invariant
`|B| + |W| + 2h ≤ rows × columns`. The pivot is White-free; if it is already
Black's, Black may play any free cell and still own all of `A ∪ {p}`. The
invariant supplies that free move and, in a nonterminal position, a free White
reply. After the two moves a strictly smaller integer height preserves the
invariant. The two White response classes preserve the child ownership and
White-free support. Transforms compose inside D4 and are injective, so the
terminal plane placement maps to an on-board placement. This is the argument
implemented by the source's `cards_sound_in` theorem.

## Provenance and trust limits

The implementation was written against these semantic definitions at source
commit `b18ed32473a6a22ebfdda98da62d61b8b1590c1e` of the reference checkout:

- `lean/Snaky/Game.lean`: exact shape, D4 placements, and legal game moves.
- `lean/Snaky/Cards.lean`: hint order, local conditions, root conditions, and
  compact parser.
- `lean/Snaky/CardsSound.lean`: support/ownership invariant, occupied-pivot
  handling, response classes, and soundness induction.
- `lean/Snaky/Bounded.lean`: the bound counts Black moves, including the last.

The compact format documentation in `tools/cards2txt.py` was also read; no
reference Python implementation is executed or imported. The exact format
index-to-matrix mapping is interface data, necessarily shared with Lean. The
terminal recognition routine instead generates orientations by reflection and
quarter-turns. Tests check that both describe the same eight symmetries.

The parser deliberately rejects malformed syntax that Lean's untrusted parser
may coerce or default: noninteger tokens, negative natural fields, invalid
orientation indices, an absent-pass marker other than `-1`, and truncation.
Accepted text has the same data interpretation. Point-list duplicates are
harmless membership repetitions. Reply lookup uses the first matching entry,
as in Lean. Unused response entries are counted. Terminal hints carry no
semantic obligation; they are not treated as additional legal branches.

This is an independent computational check, **not a kernel proof produced by
this run**. Remaining trust includes this Python implementation and its runtime,
the hand-checked correspondence to the cited definitions, and the mathematical
soundness argument. A Lean build and theorem/axiom audit are separate work.
Passing this audit establishes an upper bound for the named finite board under
those semantics. It establishes neither a lower bound nor global novelty.

The negative controls deliberately remove an inside reply and the outside
reply; break required ownership, support containment, pivot containment, D4
indices, and references; flatten a height descent; and claim a straight six-cell
row is a terminal Snaky. Additional controls cover first-match reply lookup,
truncated input, and valid extra-Black/occupied-pivot semantics.

## Concrete transcript replay

`verify_transcript.py` independently replays one outcome in the constructor's
`baseline_routes.json`. It checks every stone against actual accumulated Black
and White ownership, all claimed transforms and ownership summaries, the
selected source hints, support containment and height descent, absence of an
earlier Snaky, and the final winning placement.

```sh
python3 topics/snaky/verification/verify_transcript.py \
  topics/snaky/reference/sieben-20-cards.txt \
  topics/snaky/constructor/baseline_routes.json
```

The default requires all moves on the named finite board. `--plane` instead
permits integer-plane moves and explicitly reports any off-board cells. The
script imports only this directory's independently written card semantics; it
does not import the constructor or trust its route classifications. A legal
twenty-move replay establishes that this chosen policy and reply sequence can
take twenty moves. It does not establish a game lower bound or a universal
strategy result; those are separate statements.

## Recorded checks

The saved JSON audits include exact input and verifier SHA-256 hashes.
Focused runs passed 31 tests, followed by corruption checks on the actual
nineteen-move candidate. The compact baseline runs were sequential,
single-threaded Python 3.9.6 checks:

| Input | Cards | Inside replies | Outside classes | Root bound | Time |
| --- | ---: | ---: | ---: | ---: | ---: |
| 17×17 Sieben certificate | 1,738 | 36,625 | 1,732 | 20 Black moves | 0.935 s |
| 15×15 certificate | 8,671 | 139,698 | 8,665 | 25 Black moves | 4.004 s |

Both have six immediate-terminal cards; all cards are reachable from their
named root, and their existing hint-graph depth equals the declared root
height. The 17×17 root has 251 protected cells, 250 inside reply classes, and
38 remaining on-board cells covered by the outside class. The root free-cell
budget is `40 ≤ 289`. These are checks of existing baselines, not new bounds.

`baseline-twenty-move-transcript-audit.json` confirms the representative plane
route has twenty legal Black moves and nineteen legal White moves, follows
nineteen exact source hints, and first completes Snaky on Black move twenty.
Its White move nineteen is `(-1019,-1000)`, an actual outside-support move.
Running the same route without `--plane` correctly rejects it; the rejection
is saved as `finite-board-transcript-negative-control.json`. This does not
affect the separate finite-board certificate audit.

## Nineteen-move certificate

`snaky19-compact-audit.json` records a successful independent full check of the
pruned certificate with SHA-256
`baf8774e1fc6eea60b1756437e8b3caae0ede5e001b10c0c3787aab51840782e`.
It has 3,468 cards, all reachable, with 61,040 checked inside replies, 3,456
checked outside classes, and twelve terminal cards. Root 3,467 has empty
requirements, height and hint-graph depth nineteen, and 249 protected cells
inside `[0,16] × [0,16]`. There are 248 inside reply classes; the outside class
covers the other forty board cells and every point beyond the board. The
free-cell budget is `38 ≤ 289`. The check took 1.698 seconds.

The designated final certificate can be checked with:

```sh
python3 topics/snaky/verification/verify_cards.py \
  topics/snaky/certificate/snaky19.cards.txt --json --max-root-height 19
python3 topics/snaky/verification/check_candidate_controls.py \
  topics/snaky/certificate/snaky19.cards.txt
```

The saved audit used the identical bytes at
`constructor/snaky19.compact.cards.txt`. `snaky19-negative-controls.json`
records that changing the root height from nineteen to eighteen fails strict
descent on reply `(7,8)`, and deleting its response at `(0,4)` fails exhaustive
reply coverage. These are certificate corruption checks, not lower bounds on
the game. The larger unpruned candidate was also independently checked;
`candidate-19-audit.json` and `candidate-19-negative-controls.json` retain that
provenance.

All final checks use the original card semantics above. The Python result
supports the nineteen-Black-move upper bound through the stated soundness
argument. A formal kernel check remains a separately reported result; none
of these audit JSON files claims to perform one.

## Exact late-state obstruction

`verify_one_move.py` checks a specific eighteen-Black/eighteen-White position
reported by the earlier baseline-only constructor attempt:

```sh
python3 topics/snaky/verification/verify_one_move.py \
  topics/snaky/constructor/history_closure_20_catalog.json
```

The audit replays its eighteen legal move pairs and enumerates all translated
D4 placements intersecting a current Black stone, anchoring each of the six
shape cells at each Black cell. Every one-move win must have five existing
Black cells, so this finite enumeration covers every possible one-move
completion on the whole integer plane. The saved
`late-state-one-move-audit.json` finds 435 distinct placements: all twelve
with five Black cells are blocked; the maximum in an unblocked placement is
four. Thus this exact late position has no legal one-move win. This says
nothing about an earlier strategy choice or a game-wide lower bound.

## Separate 15×15, 24-move certificate

The independent audit in `snaky15x15-24-audit.json` checks all 8,734 reachable
cards, 144,288 inside replies and 8,728 outside classes. The empty root has
height and graph depth 24, with 220 protected cells on the 225-cell board.
Its outside class covers the other five board cells. The free-cell condition
is `48 ≤ 225`; the certificate contains six terminal cards.

`snaky15x15-24-controls.json` records rejection of a root-height change from
24 to 23 and deletion of the root's required `(0,0)` reply. These controls
are not a game lower bound. The same 31 general verifier tests apply.

```sh
python3 topics/snaky/reproduce_15x15_24.py --reconstruct
```

This serial command checks the pinned SHA-256, runs the tests and full audit,
rejects both corruptions, and reproduces both certificate and provenance map
byte for byte. It does not run Lean. The formal target and its separately
recorded status are in [RESULT-15X15-24.md](../RESULT-15X15-24.md).
