# Machine-checked results on open problems

In late September 2026, OpenAI's public [math repository](https://github.com/openai/math)
released research preprints on open problems, and the
[Big O Speedrun](https://bigospeedrun.com) keeps leaderboards for anyone who
improves their bounds. In October 2026 I worked on several of those problems,
and on open questions from recent econometrics and finance papers, with teams
of AI agents and one rule for the headline results: they only count once the
[Lean 4](https://lean-lang.org) proof assistant accepts them.

| Result | Status |
|---|---|
| [Snaky in 19 moves](#snaky-in-19-moves) | **#1 on the [Big O Speedrun leaderboard](https://bigospeedrun.com/other/snaky)**, down from 21 (OpenAI) and 20 (Sieben). Lean-checked. |
| [A tetrahedron covered by 20,000 cylinders](#covering-a-tetrahedron-with-cylinders) | About 50 times fewer cylinders than the best earlier explicit cover I found. Lean-checked. |
| [Panel moments in dynamic logit](#panel-moments-in-dynamic-logit) | Basis and exact dimension of the fixed-effect-free moments for three choices, open in Dano–Honoré–Weidner (2026). Lean-checked. |
| [Three overlapping VIX windows](#three-overlapping-vix-windows) | Option panels consistent in every pair of windows but not all three. Lean-checked in both directions. |
| [Snaky on 15×15 in 24 moves](#snaky-in-19-moves) | Improves the previous 25-move certificate for that board. Lean-checked. |
| [Sensitivity vs block sensitivity](#sensitivity-versus-block-sensitivity) | A small refinement of OpenAI's family-132 construction. Script-checked, not in Lean. |

## How the work was done

I studied the setups behind recent AI results, including the Navier–Stokes
proof, and rebuilt them for these problems. Each problem ran under a persistent
orchestrator prompt that kept an agent team working: a constructor builds the
result, a challenger attacks it along a different route, and an independent
verifier checks it.

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
· [Lean proof](topics/snaky/formal/README.md)
· [19-move package](topics/snaky/19-moves/)
· [24-move package](topics/snaky/24-moves/)
· [Novelty audit](topics/snaky/NOVELTY.md)
· [Board-size questions](topics/snaky/board_size/README.md)

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
· [Lean proof](topics/cylinder-covering/formal/README.md)
· [Full proof and reproduction](topics/cylinder-covering/README.md)
· [Comparison with published constructions](topics/cylinder-covering/RESULT.md)
· [Novelty audit](topics/cylinder-covering/NOVELTY.md)

## Panel moments in dynamic logit

Panel data with individual fixed effects are a staple of econometrics. For
dynamic multinomial logit, Dano, Honoré and Weidner
([arXiv:2610.17104](https://arxiv.org/abs/2610.17104)) construct moment
conditions that do not depend on the fixed effects, and conjecture that for
generic parameters they are linearly independent and span every such moment.
With three or more choices, both halves were open.

For three choices, two theorems are checked in Lean, each on an explicit open
dense parameter region:

- **Four periods:** their 33 moments are a basis of the moment space, for every
  initial outcome.
- **Any number of periods T:** the moment space has dimension
  3^T − C(3T, 2) + 6(T − 1).

Written proofs in `research/` go further: they extend the exact count to any
number of choices Q, prove the conjecture whenever T ≤ Q + 1, and give an
explicit basis for every T from a reordered version of their family. They are
script-checked and independently reviewed, but not yet formalized in Lean.

[Project overview](projects/econometrics-panel-moments/README.md)
· [Lean verification](projects/econometrics-panel-moments/VERIFICATION.md)
· [Exact theorems](projects/econometrics-panel-moments/THEOREM.md)
· [Manuscript](projects/econometrics-panel-moments/MANUSCRIPT.md)
· [General-Q proofs](projects/econometrics-panel-moments/research/GENERALQ_ALLT_PROOF.md)
· [Novelty audit](projects/econometrics-panel-moments/NOVELTY.md)

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
· [Lean verification](projects/vix-overlap-consistency/VERIFICATION.md)
· [Exact theorem](projects/vix-overlap-consistency/THEOREM.md)
· [Hidden-information extension](projects/vix-overlap-consistency/EXTENSION.md)
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

- **Lean 4 kernel.** Each Lean-checked theorem compiles against pinned Lean
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
- **Panel moments:** formalize the general-Q proofs in Lean, and show that
  Dano–Honoré–Weidner's own family stays a basis beyond T = Q + 1.
- **Rough-Heston option pricing** ([project](projects/rough-heston-certified-pricing/README.md)):
  a Lean-checked obstruction for a standard numerical scheme and a repair; the
  full pricing theorem is unfinished.

## Repository layout

| Path | Contents |
|---|---|
| `topics/snaky/` | Snaky certificates, proofs, checkers and Lean files |
| `topics/cylinder-covering/` | Tetrahedron cover construction, proof and Lean files |
| `projects/econometrics-panel-moments/` | Panel-moment theorems, manuscript, certificates and Lean files |
| `projects/vix-overlap-consistency/` | SPX/VIX theorem, extension, certificates and Lean files |
| `topics/sensitivity-separation/` | Sensitivity note, checks and reproduction scripts |
| `projects/rough-heston-certified-pricing/` | Rough-Heston obstruction, repair and Lean files (in progress) |

Each package's README gives its reproduction command. Files named `STATE.md`
or `STATUS.md` are unedited working logs, and `research/` folders hold work in
progress.
