# MGAP4D Lean Skeleton Bundle

This ZIP contains the Lean skeletons corresponding to the MGAP4D v1.0-final / v1.6 proof-kernel conversation.

## Contents

- `MGAP4D/R1/Basic.lean`  
  R1 scaffold layer: physical input ledger, Hilbert-space construction, vacuum sector, Hamiltonian seed, excited-sector scaffold.

- `MGAP4D/R2/Basic.lean`  
  R2 operator layer: closed form, self-adjoint nonnegative Hamiltonian, vacuum/excited reducing decomposition, H_exc.

- `MGAP4D/R3/Basic.lean`  
  R3 spectral square-root route: nonnegative operator sqrt, zero form -> kernel, shifted operator route.

- `MGAP4D/R4/Basic.lean`  
  R4 exact lower-bound skeleton: decomposition ledger, receipts, exact rational constant assembly C_R4 = 33/20, operator order bridge.

- `MGAP4D/R5/Basic.lean`  
  R5 spectrum set construction: excited spectrum, infimum, lower-bound bridge, total spectrum decomposition.

- `MGAP4D/R6/Basic.lean`  
  R6 no-spectrum interval: conditional and unconditional activation of σ(H) ∩ (0, 33/20) = ∅.

- `MGAP4D/R7/Basic.lean`  
  R7 eigenstate attainment: saturation subspace, F1--F5 atom-persistence skeleton, exact gap equality m_exc = 33/20.

- `MGAP4D/Global/FinalAssembly.lean`  
  Global assembly connecting R1--R7 to the final theorem packet and public claim boundary.

- `MGAP4D.lean`  
  Top-level imports.

- `lakefile.lean`, `lean-toolchain`

## Important status note

The Lean files are intentionally Prop-level proof-kernel skeletons. They contain no `sorry`, `admit`, `axiom`, or `constant`. They encode closure dependencies and proof obligations as structures and theorem-pack functions.

The mathematical target remains:

```text
m_gap = 33/20
there exists an eigenstate ψ* with H_exc ψ* = (33/20) ψ*
33/20 ∈ σ_p(H_exc)
```

Public Clay-level claim remains review-gated until external independent verification.

## How to check

```bash
lake build
```

## License

Use according to the license selected for the public release package.
