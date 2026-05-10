# Dependency Summary

- Generated: `2026-05-10T05:57:38.006183+00:00`

## Work unit order
1. `WU-R1-ELL-CLM`
2. `WU-R1-PROJECTION`
3. `WU-R2-REDUCING-SPECTRUM`
4. `WU-R4-LOWER-BOUND`
5. `WU-R3-UNBOUNDED-KERNEL`
6. `WU-R7-ATOM-EXACT-GAP`
7. `WU-GLOBAL-FINAL-AUDIT`

## Critical edges
- `WU-R1-ELL-CLM` → `WU-R1-PROJECTION`: ell_CLM enables kernel/projection
- `WU-R1-PROJECTION` → `WU-R2-REDUCING-SPECTRUM`: P_vac/P_exc imported by R2
- `WU-R2-REDUCING-SPECTRUM` → `WU-R4-LOWER-BOUND`: H_exc self-adjoint is R4 input
- `WU-R4-LOWER-BOUND` → `WU-R3-UNBOUNDED-KERNEL`: K_exc nonnegative
- `WU-R4-LOWER-BOUND` → `WU-R5-FINAL-SURFACE`: spectrum subset
- `WU-R3-UNBOUNDED-KERNEL` → `WU-R7-ATOM-EXACT-GAP`: K_exc psi = 0
- `WU-R7-ATOM-EXACT-GAP` → `WU-GLOBAL-FINAL-AUDIT`: m_exc = 33/20

## Terminal gate
- mathematical_gate: requires all theorem replacements
- audit_gate: requires clean build and independent replay
- public_gate: review gated
