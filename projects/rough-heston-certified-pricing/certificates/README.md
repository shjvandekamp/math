# Verification evidence

The exact certificate is the Lean proof term reconstructed from the project sources and checked by the pinned Lean kernel. `./verify.sh` rebuilds every project proof module after deleting only its own generated outputs, then records `#print axioms` for the headline declarations.

- `clean-build.log`: final clean compilation command output and exit status.
- `axioms.txt`: dependency-closure axiom output and headline types.
- `toolchain.txt`: actual compiler identity.

Numerical discovery output lives in `discovery/` and is not a proof certificate. No unchecked numerical solver, `native_decide`, or external oracle establishes a theorem.
