# Closure Dependency DAG

- Generated: `2026-05-10T05:33:14.341533+00:00`

## Edges
- `R1_ell_CLM` → `R1_kernel_closed`: kernel is defined through ell
- `R1_kernel_closed` → `R1_projection_pair`: closed excited sector enables projection
- `R1_projection_pair` → `R2_projection_commutation`: R2 imports vacuum/excited projections
- `R2_projection_commutation` → `R2_reducing_subspace`: commutation gives reducing subspace
- `R2_reducing_subspace` → `R2_H_exc_selfadjoint`: restriction self-adjointness
- `R2_H_exc_selfadjoint` → `R4_form_lower_bound`: lower bound is on H_exc/q_exc
- `R4_form_lower_bound` → `R4_operator_order`: form lower bound exports operator order
- `R4_operator_order` → `R5_spectrum_subset`: spectral order gives subset
- `R5_spectrum_subset` → `R6_gap_interval_empty`: gap interval exclusion
- `R4_operator_order` → `R3_shifted_operator_nonnegative`: shifted operator K_exc >= 0
- `R3_shifted_operator_nonnegative` → `R3_zero_form_kernel`: sqrt route for kernel
- `R3_zero_form_kernel` → `R7_atom_exact_gap`: atom vector becomes eigenvector
- `R7_atom_exact_gap` → `GLOBAL_final_theorem`: exact gap assembly

## Work-unit chain
1. `WU-R1-ELL-CLM`
2. `WU-R1-PROJECTION`
3. `WU-R2-REDUCING-SPECTRUM`
4. `WU-R4-LOWER-BOUND`
5. `WU-R3-UNBOUNDED-KERNEL`
6. `WU-R7-ATOM-EXACT-GAP`
7. `WU-GLOBAL-FINAL-AUDIT`

## Gate notes
- public gate remains closed until independent replay
- mathematical gate requires theorem replacements
- audit gate requires clean build and residual review
