# P4-Q2-PZ37AKB — original third-power Haar–Cauchy floor

2026年11月12日 JST。本文は固定Lean4カーネルによる形式証明の説明記録であり、本文自体は証明ではない。

## 1. Primary source and exact kernel certification

- Repository `itakura-hidetoshi/4d-mass-gap`; theorem canonical branch `formal/real-hilbert-uniform-coercive-strong-limit`; `main` is a documentary mirror.
- [Theorem PR #6659](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6659) MERGED by exact-head squash. Final source HEAD `85ca5eb4575fbc89d69fd43eb17d9316bad0c4bf`; formal squash HEAD `b508a059daa252507f02ec175143d975188556c9`.
- [Exact-source PR CI #43104537528](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43104537528) `completed/SUCCESS`: actual changed-Lean job and Lean step `completed/SUCCESS`; dependency closure **11,442/11,442**. Independent completion-receipt job `completed/SUCCESS`; exact-head status `chatgpt-ci-receipt/PR Lean Fast Check` success.
- [Formal post-merge push CI #43105393399](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43105393399), `event=push`, independently `completed/SUCCESS` at exact squash HEAD. Changed-Lean job and Lean step `completed/SUCCESS`, **11,442/11,442**, separate completion-receipt job `completed/SUCCESS`, exact-head commit status success.
- All eight declarations' individual `#print axioms` outputs consist exclusively of `propext`, `Classical.choice`, `Quot.sound`. New `sorryAx` absent; changed AKB error/warning 0/0.
- Exact source, GitHub test merge and formal squash have identical Git tree `388f6a17df60650a9191d47e388e3f8da9e93970`. Only one added Lean leaf, 269 lines; zero preexisting file edits/deletions. Initial failure at line 84 arose from the pinned Lean API: `mul_le_mul_left` takes a comparison, not a positive multiplier, and returns a function rather than an iff. Replacing it with `(mul_le_mul_iff_of_pos_left hFirstPos).mp` fixed elaboration without changing any theorem statement.
- New leaf: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalThirdPowerHaarCauchyFloorV5_PZ37AKB.lean`; direct imports AKA, `Mathlib.Analysis.InnerProductSpace.Projection.Basic` and `Mathlib.Tactic`. Pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## 2. Proven mathematics and scope

For each finite spatial slice `H : ℕ` and `β>0`, let `S` be the original normalized physical SU(2) Wilson one-slab operator, `f₀` the original centered signed ZW source, `V=‖f₀‖²>0` its genuine Haar variance, and `B=m²·Measure.real(μ_H)({u<-m})>0` the original AJA negative-margin Haar certificate.

The original physical operator is symmetric. Cauchy–Schwarz in the actual real Hilbert space yields the successive inequalities
```
a₁² ≤ a₀·a₂,      a₂² ≤ a₁·a₃,
a₀=‖f₀‖²=V;       a₁=‖Sf₀‖²;      a₂=‖S²f₀‖²;      a₃=‖S³f₀‖².
```
Because the original certificate gives `0<B≤a₁`, positive cancellation implies `a₁³≤a₀²a₃`. Therefore the **actual finite-H Wilson third-power lower floor** is
```
0 < B³/V² ≤ ‖S³f₀‖².
```
The genuine AJX cap `B≤V/16` also implies `B³/V²<B`, so this floor by itself does not exclude a strictly smaller third-power energy. A third-power AJA witness is a separate **unproved** upper bound `‖S³f₀‖²<B`. **Only under that additional premise** is the interval `B³/V²≤‖S³f₀‖²<B` certified.

## 3. Eight certified Lean declarations

1. `realHilbert_symmetric_shiftedSecondPower_normSq_Cauchy_akb`
2. `realHilbert_symmetric_thirdPower_normSq_Cauchy_akb`
3. `realHilbert_oneStep_margin_thirdPower_Cauchy_akb`
4. `GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_cube_le_varianceSq_mul_energy`
5. `GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_energy_ge_cube_div_varianceSq`
6. `GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_energy_pos`
7. `GroundStatePosteriorJoint.p4Q2PZ37AKB_originalAJA_cube_div_varianceSq_lt_AJA`
8. `GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_AJA_witness_interval`

All are in namespace `MGAP4D.MathlibAnalytic`. Full source signatures and eight axiom outputs are in the certified Lean artifacts.

## 4. Remaining obstruction (NO_DATA)

Neither `n=2` nor `n=3` original AJA strict witness has been constructed, and their nonexistence is not proven. Quantitative upper bounds on the actual finite-power energy and independent full-top residual remain OPEN. Top eigenspace one-dimensionality, spatial-volume-uniform coercivity, Hamiltonian spectral gap and four-dimensional continuum Yang–Mills mass gap are OPEN. A lower floor or conditional interval cannot be illicitly upgraded to a strict upper witness.

Append-only / tighten-only / overwrite-forbidden / same-root. Original Wilson/Haar/ZW/AJA quantities, hypotheses, theorem statements and pinned environment unchanged.
