# Machine-checked results on open problems

In late September 2026, OpenAI's public [math repository](https://github.com/openai/math)
released a set of research preprints on open problems, and the
[Big O Speedrun](https://bigospeedrun.com) keeps leaderboards for anyone who
improves their bounds. In October 2026 I worked on four of those problems, plus
one from recent SPX/VIX research, with AI assistance and one rule: a result only
counts if the [Lean 4](https://lean-lang.org) proof assistant accepts it.

Every headline theorem here is checked by Lean's kernel, rebuilt from pinned
sources, and cross-checked by verification code written separately from the
construction.

## Highlights

| Result | Where it stands |
|---|---|
| **[Snaky in 19 moves](#snaky-in-19-moves)**: Maker wins the Snaky game on the infinite board within 19 moves | **#1 on the [Big O Speedrun Snaky leaderboard](https://bigospeedrun.com/other/snaky)**, after 21 (OpenAI) and 20 (Sieben). Lean-checked. |
| **[Snaky on 15×15 in 24 moves](#snaky-in-19-moves)** | Improves the previous 25-move certificate for that board. Lean-checked. |
| **[A tetrahedron covered by 20,000 cylinders](#covering-a-tetrahedron-with-cylinders)**, normalized cost below 0.499922 | About 50 times fewer cylinders than the best earlier explicit cover I found, with a far larger saving. Lean-checked. |
| **[Three overlapping VIX windows](#three-overlapping-vix-windows)**: option panels consistent in every pair of windows but not all three | Exact margin, both directions Lean-checked. |
| **[Sensitivity vs block sensitivity](#sensitivity-versus-block-sensitivity)**: explicit labels and sharper counting for OpenAI's family-132 construction | A small refinement; other manuscripts report larger exponents. |

## Snaky in 19 moves

In Frank Harary's "animal tic-tac-toe", two players take turns claiming cells
of a square grid. Maker wins by owning a copy of a given shape; Breaker only
blocks. Snaky is the six-cell shape that stayed the open case for decades.
Recent work showed Maker wins and turned it into a race: OpenAI's September
preprint needed 21 moves, then Nándor Sieben's strategy needed 20.

My certificate wins within **19 of Maker's own moves** against every Breaker
reply, on the infinite board and on 17×17. It extends Sieben's 20-move strategy
with tactics from Trevor Morris's 15×15 work, has 3,468 positions ("cards"),
and is checked reply by reply in Lean. It is listed first on the
[Big O Speedrun leaderboard](https://bigospeedrun.com/other/snaky).

A second certificate wins on the **15×15 board in 24 moves**, improving the
previous 25 (8,734 cards, 89 of them new). Two board-size questions, Maker on
an empty 14×14 board and Breaker on 10×10, are still open.

[Proof note (PDF)](topics/snaky/output/pdf/snaky-note.pdf)
· [19-move package](topics/snaky/19-moves/)
· [24-move package](topics/snaky/24-moves/)
· [Novelty audit](topics/snaky/NOVELTY.md)
· [Board-size research and open questions](topics/snaky/board_size/README.md)

## Covering a tetrahedron with cylinders

How cheaply can a regular tetrahedron be covered by infinitely long cylinders?
The cost is the total cross-section area, divided by the area of the
tetrahedron's smallest shadow. Published constructions show this can go below
1/2, but their explicit versions get only a tiny bit below it: the best earlier
explicit cover I found uses about a million cylinders to get 5.7·10⁻¹⁰ below 1/2.

This cover uses **20,000 cylinders** and gets about **7.8·10⁻⁵ below 1/2**
(certified cost below 0.499922). The proof that it covers the whole closed
tetrahedron, with the exact count and error bounds, is formalized in Lean.
This is a comparison with the published explicit constructions, not a claim
of optimality.

[Mathematical note (PDF)](topics/cylinder-covering/output/pdf/cylinder-covering-note.pdf)
· [Full proof and reproduction](topics/cylinder-covering/README.md)
· [Comparison with published constructions](topics/cylinder-covering/RESULT.md)
· [Lean proof](topics/cylinder-covering/formal/README.md)
· [Novelty audit](topics/cylinder-covering/NOVELTY.md)

## Three overlapping VIX windows

The VIX is read off S&P 500 option prices over a window of future dates.
Given option prices for several overlapping windows, can one market model
explain all of them at once? Recent working papers study this for two windows.

This project builds explicit SPX/VIX option panels where every single window
and every pair of windows fits one finite market model, but the three windows
together do not, with an exact separation margin of (1−30ε)/32. A follow-up
theorem shows the same panel becomes consistent once the model may contain
hidden activity and signals. So the contradiction comes from what the market is
assumed to reveal, not from the prices alone. Both directions are checked in
Lean. This is a model-consistency result, not an arbitrage claim.

[Manuscript](projects/vix-overlap-consistency/MANUSCRIPT.md)
· [Exact theorem](projects/vix-overlap-consistency/THEOREM.md)
· [Hidden-information extension](projects/vix-overlap-consistency/EXTENSION.md)
· [Lean verification](projects/vix-overlap-consistency/VERIFICATION.md)
· [Novelty audit](projects/vix-overlap-consistency/NOVELTY.md)

## Sensitivity versus block sensitivity

For a Boolean function, sensitivity counts the single bits whose flip changes
the output; block sensitivity counts disjoint groups of bits that do.
OpenAI's family-132 preprint separates the two by a power just above 2.

This note makes that construction's tournament labels explicitly computable
and sharpens one counting step, which moves the certified exponent from about
2.0154112 to 2.0154115. It is a refinement of that construction only: other
manuscripts report larger exponents (about 2.032 and 2.027), and the note
cites them.

[Mathematical note (PDF)](topics/sensitivity-separation/output/pdf/sensitivity-note.pdf)
· [Overview and reproduction](topics/sensitivity-separation/README.md)
· [Novelty audit](topics/sensitivity-separation/publication/NOVELTY_AUDIT.md)
· [Follow-up review](topics/sensitivity-separation/publication/FOLLOWUP_REVIEW.md)

## How the results are checked

- **Lean 4 kernel.** Each headline theorem compiles against pinned Lean
  (4.34.1) and Mathlib versions, and a kernel audit confirms it uses only the
  standard axioms.
- **Independent checkers.** Certificates are re-checked by separately written
  code, including deliberately corrupted inputs that the checkers must reject.
- **Novelty audits.** Each topic pins the sources it builds on to exact commits
  and separates what is new from what is inherited or only computational
  evidence.
- **Stated limits.** The work was developed with AI assistance. Lean checks
  the proofs, not their novelty, and none of this has been peer reviewed, so
  priority claims are provisional.

## Open work

- **Snaky:** an 18-move strategy, and the empty 14×14 and 10×10 board-size
  questions ([what was tried](topics/snaky/board_size/FUTURE_RESEARCH.md)).
- **Rough-Heston option pricing** ([PR #4](https://github.com/shjvandekamp/math/pull/4)):
  a Lean-checked obstruction for a standard numerical scheme and a repair; the
  full pricing theorem is unfinished.

## Repository layout

| Path | Contents |
|---|---|
| `topics/snaky/` | Snaky certificates, proofs, checkers and Lean files |
| `topics/cylinder-covering/` | Tetrahedron cover construction, proof and Lean files |
| `topics/sensitivity-separation/` | Sensitivity note, checks and reproduction scripts |
| `projects/vix-overlap-consistency/` | SPX/VIX theorem, extension, certificates and Lean files |

Each package's README gives its reproduction command. Files named `STATE.md`
and the `research/` and `notes/` folders are the unedited working logs.
