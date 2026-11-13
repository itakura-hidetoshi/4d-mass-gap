# P4-Q2-PZ37AKW — original H<=21 SU(2) small-coupling third-Taylor AJA/top comparison

Date: 2026-11-13 JST.
Canonical theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Actual original-model theorem and boundary

Preserve the original complete finite-volume SU(2) Wilson one-slab
physical transfer P, normalized S=P/||P||, genuine centered ZW signed
physical source f0_H, original AIG normalized negative margin m_H,
original normalized transfer representative u_H, genuine product Haar
probability mu_H, genuine full-top eigenspace projection Q, and the
**strict original** AJA budget

```text
B_(H,beta0) = m_(H,beta0)^2 * mu_H{U:u_(H,beta0)(U)<-m_(H,beta0)}
beta0 = log(3/2)/64
p_H = 24*(H+1)^3
```

The pinned mathlib theorem `Real.exp_bound` at n=3 gives
`|exp(x)-(1+x+x²/2)| <= 2*|x|³/9` for |x|<=1.
At the *unchanged original fixed coupling upper bound*
`beta0<=1/156`, restrict to |x|<=1/156, retaining
`|x|³ <= x²/156`. Hence:

```text
exp(x) <= 1+x+(176/351)*x²
```

The original Haar one-link character chi has zero mean, |chi|<=1,
and exact true SU(2) Haar second moment E[chi²]=1/4 (ACK/AKS).
Integrating the genuine original Haar expression (NOT a replacement
Gaussian probability) proves, for 0<=beta<=1/156:

```text
mgf_chi_original(beta) <= 1 + (44/351)*beta²
z_original(beta) <= exp(-beta+(44/351)*beta²)
Z_H_original_crossing(beta) <= exp(p_H*(-beta+(44/351)*beta²))
```

The exact original plaquette bound H<=21 -> p_H<=255552 and
already-certified `beta0<=1/156` yield the rational certificate

```text
(44/351)*beta0²*p_H <= (44*255552)/(351*156²)
                      <= 11/8 <= log 4.
```

The original negative-region Haar mass r_H is at most 1 solely
because genuine mu_H is a probability, NOT because its numerical
value was computed. This discharges the unchanged AKQ genuine
partition–Haar sufficient condition:

```text
r_H * Z_H_original_crossing(beta0) <= 4*exp(-beta0*p_H).
```

AKQ and AKU consequently yield the two distinct ORIGINAL-model
results, for every finite natural H<=21:

```text
NOT exists n : Nat:
    ||S_(H,beta0)^n f0_H||² < B_(H,beta0)

B_(H,beta0) <= ||Q_(H,beta0) f0_H||²
Delta_H := B_(H,beta0) - ||Q_(H,beta0) f0_H||² <= 0.
```

H=19,20,21 are new beyond AKV's H<=18; an explicit H21
no-witness declaration is present. No actual r_H numerical mass,
Delta_H strict negativity or equality, H>=22 result, H-uniform
GL Rayleigh lower bound, Hamiltonian spectral gap, or continuum
four-dimensional Yang–Mills mass gap has been proved.

## Exact-source Lean4 certification and provenance

New Lean module (append-only):
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH21SmallCouplingThirdTaylorAJANoGoV5_PZ37AKW.lean`.
Twelve `#print axioms` audits:

1. `real_exp_le_one_add_oneSeventySixThreeFiftyOne_sq_akw`
2. `p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment`
3. `p4Q2PZ37AKW_originalSingleLinkCharacter_mgf_le_fortyFourThreeFiftyOne`
4. `p4Q2PZ37AKW_originalSingleLinkPartition_le_fortyFourThreeFiftyOneGaussian`
5. `p4Q2PZ37AKW_originalCrossingPartition_le_fortyFourThreeFiftyOneGaussian`
6. `p4Q2PZ37AKW_originalPlaquetteCount_le_twentyOne`
7. `p4Q2PZ37AKW_originalFixedCoupling_fortyFourThreeFiftyOneBudget_le_logFour`
8. `p4Q2PZ37AKW_originalFixedCoupling_partitionHaarMass_of_le_twentyOne`
9. `p4Q2PZ37AKW_originalFixedCoupling_le_twentyOne_no_AJA_power_witness`
10. `p4Q2PZ37AKW_originalH21_no_AJA_power_witness`
11. `p4Q2PZ37AKW_originalFixedCoupling_budget_le_fullTop_of_le_twentyOne`
12. `p4Q2PZ37AKW_originalFixedCoupling_topHaarResidual_nonpos_of_le_twentyOne`

[Theorem PR #6715](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6715)
MERGED into canonical formal by squash
`d250db7baffefdaeb02b399e8a528ec407a53646`.
Authenticated exact-source HEAD:
`861d23d3940f766616562632ac89534638b47444`.
Source/test-merge/squash shared Git tree:
`0ce53f3e6d88692b58e2ab73b41f5a2afaf3bbb3`.

[Exact-source CI #43345340030](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43345340030):
completed/**SUCCESS**, pinned Lean dependency closure **11,458/11,458**,
12/12 new declarations depend only on the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
No new `sorryAx`, changed AKW warning/error **0/0**.
Independent exact-HEAD completion receipt
job `131625496418` completed/SUCCESS, GitHub status `success`.
Earlier CI [#43344935766](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43344935766)
was cancelled after the source update that corrected an inherited
H=18 bound and H=18 centered-source index in the explicit H21
specialization. The theorem statements and original physics were
never weakened; no existing Lean file was modified.

The separately triggered actual canonical formal squash
[push CI #43362764404](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43362764404)
must be authenticated only after completed/SUCCESS, with its own
exact-HEAD completion receipt. At record creation it is
**not yet certified**. Append the later receipt without overwriting
this historical pre-completion observation.

Pinned Lean v4.30.0-rc2; pinned mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
All prior Wilson/Haar/source/budget, Lean files, root, assumptions,
workflows, and pinned environment unchanged.
append-only / tighten-only / overwrite-forbidden / same-root.

## Remaining obstruction

Only original H<=21 AJA no-witness and B_H<=||Qf0_H||²
(with Delta_H<=0) are certified.
Strict Delta_H<0 versus equality, numerical actual r_H,
H>=22, uniform GL coercivity, Hamiltonian spectral gap and
continuum four-dimensional Yang–Mills mass gap remain OPEN.
The inability to produce an AJA witness is NOT a mass-gap proof.
When mirrored to main, preserve this exact proof-record Git blob
and append only the corresponding README/ROADMAP notes.
