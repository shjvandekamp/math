import PanelMoments.WitnessEvaluation
import PanelMoments.WitnessSource

/-!
# Concrete rank witnesses, checked from the model primitives

`WitnessCore` proves the algebraic model bridges. Independent generated row
modules check the finite-field formulas and right inverses in Lean's kernel.
The two aggregators lift those exact certificates to nonzero real determinants.
No native-code oracle or external determinant result is assumed.

For a clean build, compile `WitnessData`, `WitnessRows`, and `WitnessCore` first, then the modules
listed by `exploration/generate_lean_witness.py --list-modules` sequentially, then
this facade. Building it directly may schedule uncached row modules concurrently.
-/
