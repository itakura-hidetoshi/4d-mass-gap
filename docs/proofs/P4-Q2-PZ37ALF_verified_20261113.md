# P4-Q2-PZ37ALF — explicit original Haar identity-box floor for true Wilson norm

2026-11-13 JST. Canonical: `formal/real-hilbert-uniform-coercive-strong-limit`.
[Theorem PR #6740](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6740) **MERGED**, canonical squash `1d1e2e62769b255defede21b394ab72c89720ed8`. Exactly one new append-only Lean4 leaf `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalIdentityBoxExplicitPhysicalNormFloorV5_PZ37ALF.lean` (193 lines; 7 declarations with 7 matching axiom audits). Original Wilson SU(2), centered ZW physical source and its Haar representative, crossing/full slab kernels and both original spatial halfweights, actual physical transfer norm, normalized spatial Haar, fixed beta0, AJA margin/budget and top projection, all older Lean files, pinned toolchain and roots are unchanged.

## Original-model mathematical statement

Use the genuine AHN true-Haar identity-box source variance floor
`vBox_H := (3*p_H/8)^2 * κ(1/96)^card(Link_H)`, where `κ` is the actual ADQ Haar sphere-ball lower fraction and `Link_H` the original finite spatial link type. AHN certifies `0 < vBox_H <= V_H` at every original finite H; ALF retains that **same** geometric number, rather than substituting a Gaussian source or assumed probability table.

ALE independently proves the unchanged exponential crossing kernel satisfies `Kcross_H(beta,A,B) >= kFloor_H(beta)=exp(-2*beta*ell_H)>0` for `beta>=0`, and the original crossing-weighted source-square moment satisfies `M2pair_H(beta)>=2*kFloor_H(beta)*V_H`. ALF derives
`M2pair_H(beta) >= 2*kFloor_H(beta)*vBox_H > 0`,
and, via ALD's original physical one-slab operator norm and exact two-halfweight Wilson pair integration,
`||P_H(beta)|| >= exp(-beta*p_H) * [Zcross_H(beta) + (beta^2/4)*(2*kFloor_H(beta)*vBox_H)]`
for every finite H and `beta>=0`.

The extra correction is independently proved **strictly positive** when `beta>0`, so ALF also gives the strict comparison with the old AIW original spatial-mean norm floor. It includes exact original `H=22`, `beta0=log(3/2)/64` and `p22=292008`, retaining the true finite geometric link power. This is an explicit positive finite-volume correction, NOT a uniform-in-H lower bound or new AJA conclusion.

## Seven new audited declarations

1. `p4Q2PZ37ALF_originalIdentityBoxVarianceFloor`
2. `p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos`
3. `p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_le_sourceVariance`
4. `p4Q2PZ37ALF_originalPairSecondMoment_ge_identityBoxFloor`
5. `p4Q2PZ37ALF_originalPhysicalNorm_ge_identityBoxFloor`
6. `p4Q2PZ37ALF_originalPhysicalNorm_strictly_gt_spatialMean_viaBox`
7. `p4Q2PZ37ALF_originalH22_fixedCoupling_physicalNorm_ge_box`

## Actual Lean4 authentication and error provenance

Initial exact source `d5e7a34219e93748cd3120cf506be02949465f6d` failed [PR CI #43429957641](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43429957641), with exactly one direct changed-file Lean error at line 133: using `add_le_add_left hScaled` produced `correction + Zcross` instead of the goal `Zcross + correction`. The failed elaboration infected three dependent axiom prints with `sorryAx`, which are **not** certified. No theorem statement or original physics was changed by the repair.

Fixed source `2fc5516febed427c4803ea622a22c6f2c2cca83f` uses `linarith only [hScaled]` to preserve the required additive order. Final [exact-source PR CI #43431005872](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43431005872) **completed/SUCCESS** with pinned Lean v4.30.0-rc2 and mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`. Actual dependency closure **11,468/11,468**; all **7/7** new `#print axioms` limited to `propext`, `Classical.choice`, `Quot.sound`, new `sorryAx` absent, changed ALF warning/error **0/0**. Changed-Lean job `131904187301` and independent completion receipt job `131906641953` both completed/SUCCESS. Actual log:
`[mcp-receipt] event=pull_request exact_sha=2fc5516febed427c4803ea622a22c6f2c2cca83f source_result=success run=43431005872 attempt=1`.

Independent Git commit checks show the same source, PR test-merge and squash tree `c320a2519759fb3c56e5a95e0f4ddb0d4db9bd3e`. The theorem integrated squash is `1d1e2e62769b255defede21b394ab72c89720ed8`.

## Canonical formal push — initial pending checkpoint

The independent [formal push CI #43431959352](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43431959352), keyed to exact squash HEAD `1d1e2e62769b255defede21b394ab72c89720ed8`, was **in_progress** at the initial record observation. Do not promote it to SUCCESS until completed workflow, exact Lean job, 7 axiom audits and independent receipt have been re-observed. Append the actual final receipt after verification; preserve this historical pending checkpoint.

## Unresolved physical and mathematical obstruction

The AHN identity-box factor `κ(1/96)^card(Link_H)` is a real finite positive Haar floor but may be extremely small at large H; no positive H-uniform coercivity or mass gap follows. The original H22 strictly negative Haar mass upper condition required by AKX remains **NO_DATA**, so unconditional AJA witness nonexistence has not been proved. At H>=25 the OLD AKX scalar sufficient premise is impossible, which does not imply AJA witnesses exist. Neither a Hamiltonian spectral gap nor the continuum four-dimensional Yang–Mills mass gap has been established.

Next valid task: compare this genuinely certified but very small ALF norm correction with actual original AJA/top budget inequalities while retaining the directional inequalities, or independently prove original H22 complementary positive-side Haar-cell masses in AKY. Do not replace unresolved H22 mass with a scalar threshold compatibility argument.

Append-only / tighten-only / overwrite-forbidden / same-root.
