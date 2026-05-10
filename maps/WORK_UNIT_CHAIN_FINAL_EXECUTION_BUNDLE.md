# Work Unit Chain Final Execution Bundle

- Generated: `2026-05-10T05:53:23.407965+00:00`

## Chain
1. `WU-R1-ELL-CLM`
   - output: ell_CLM
2. `WU-R1-PROJECTION`
   - input: ell_CLM
   - output: P_vac/P_exc export to R2
3. `WU-R2-REDUCING-SPECTRUM`
   - input: P_vac/P_exc
   - output: H_exc self-adjoint and spectrum union
4. `WU-R4-LOWER-BOUND`
   - input: H_exc self-adjoint
   - output: H_exc >= 33/20 I
5. `WU-R3-UNBOUNDED-KERNEL`
   - input: K_exc := H_exc - 33/20 I >= 0
   - output: zero form implies eigenkernel
6. `WU-R7-ATOM-EXACT-GAP`
   - input: K_exc psi = 0 and atom persistence
   - output: m_exc = 33/20
7. `WU-GLOBAL-FINAL-AUDIT`
   - output: final theorem packet and public gate

## Final gate
- Lean replay gate
- independent review gate
- public wording gate
