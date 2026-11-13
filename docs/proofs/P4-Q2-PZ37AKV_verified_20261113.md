# P4-Q2-PZ37AKV — genuine original SU(2) H<=18 AJA and full-top/Haar residual

Date: 2026-11-13 JST. Canonical theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Actual original-model theorem

The original complete finite SU(2) Wilson one-slab physical operator P,
normalized physical S=P/||P||, true full-top eigenspace projection Q,
genuine signed centered ZW source f0_H, true Haar product probability,
original negative-set E_H={u_(H,beta0)<-m_(H,beta0)}, original AIG
margin, p_H=24(H+1)^3 and strict AJA budget
`B_(H,beta0)=m_(H,beta0)^2*mu_H(E_H)` remain unchanged.
The fixed coupling is `beta0=log(3/2)/64`.

The pinned mathlib theorem `Real.exp_bound` with n=3 certifies the
pointwise inequality `exp(x)<=1+x+13*x^2/18` on |x|<=1, since the
third Taylor remainder is at most `2*|x|^3/9 <= 2*x^2/9`.
The ALREADY certified true SU(2) single-link character has zero
normalized Haar mean, support in [-1,1] and second moment exactly 1/4.
The original unchanged one-link Haar MGF and AIF crossing partition
therefore satisfy

```text
mgf_original(beta) <= 1 + 13*beta^2/72
Z_H(beta) <= exp(p_H * (-beta + 13*beta^2/72))
```

for 0<=beta<=1. This is an improved bound on the genuine original
integral, not an artificial Gaussian measure or altered transfer kernel.

For H<=18, exact p_H<=164616, existing beta0<=1/156 and
`11/8<=log(4)` give
`13*beta0^2*p_H/72 <= (6859/5616) <= 11/8 <= log(4)`.
The *true* negative-region Haar mass satisfies `r_H<=1` by
probability, without a numerical measurement. Hence the unchanged AKQ
partition-Haar sufficient condition
`r_H*Z_H(beta0)<=4*exp(-beta0*p_H)` holds for H<=18.

The original AKQ strict AJA no-witness theorem and AKU genuine
full-top/Haar budget theorem now imply the two separate results:

```text
for all H : Nat, H<=18:
  not exists n : Nat, ||S_(H,beta0)^n f0_H||^2 < B_(H,beta0)
  B_(H,beta0) <= ||Q_(H,beta0) f0_H||^2
  Delta_H := B_(H,beta0)-||Q f0_H||^2 <= 0
```

H=17 and H=18 are NEW extensions beyond AKT/AKU's H<=16 range.
An explicit H18 no-witness declaration was separately checked.
No numerical r_H, strict `Delta_H<0` or `Delta_H=0`, H>=19
comparison, H-uniform GL Rayleigh coercivity, Hamiltonian spectral
gap or continuum four-dimensional Yang--Mills mass gap is proved.

## Exact Lean4 source and machine verification

New source:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH18ThirdTaylorAJANoGoV5_PZ37AKV.lean`.

Twelve declarations, all `#print axioms` audited:
1. `real_exp_le_one_add_thirteenEighteenths_sq_akv`
2. `p4Q2PZ37AKV_originalSingleLinkCharacter_secondMoment`
3. `p4Q2PZ37AKV_originalSingleLinkCharacter_mgf_le_thirteenSeventyTwo`
4. `p4Q2PZ37AKV_originalSingleLinkPartition_le_thirteenSeventyTwoGaussian`
5. `p4Q2PZ37AKV_originalCrossingPartition_le_thirteenSeventyTwoGaussian`
6. `p4Q2PZ37AKV_originalPlaquetteCount_le_eighteen`
7. `p4Q2PZ37AKV_originalFixedCoupling_thirteenSeventyTwoBudget_le_logFour`
8. `p4Q2PZ37AKV_originalFixedCoupling_partitionHaarMass_of_le_eighteen`
9. `p4Q2PZ37AKV_originalFixedCoupling_le_eighteen_no_AJA_power_witness`
10. `p4Q2PZ37AKV_originalH18_no_AJA_power_witness`
11. `p4Q2PZ37AKV_originalFixedCoupling_budget_le_fullTop_of_le_eighteen`
12. `p4Q2PZ37AKV_originalFixedCoupling_topHaarResidual_nonpos_of_le_eighteen`

[Theorem PR #6712](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6712)
MERGED with exact authenticated source
`af98ad2279e3698c8f6d9ebcde531d66d600fc4f`,
canonical formal squash
`da81af5042b1dcab219912423d966c982ef0c351`,
source/test-merge/squash common Git tree
`6878c4853cc8e790a96c7b437998b386be4178de`.

[Exact-source CI #43341670288](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43341670288)
completed **SUCCESS**: pinned Lean build **11,457/11,457**;
12/12 axiom prints only `propext`, `Classical.choice`, `Quot.sound`;
no new `sorryAx`, changed AKV warning/error **0/0**, and exact-head
completion receipt completed/SUCCESS with commit status `success`.

Provenance of elaboration repair: first [CI #43339902043](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43339902043)
failed from a duplicate local `beta0` notation and an inherited old
quarter coefficient where `13/72` was required. The corrected
[CI #43340926874](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43340926874)
proved all twelve statements but reported three tactic-linter warnings;
the final CI #43341670288 eliminates those without changing the
theorem statements. No prior Lean source modified.

An independent actual canonical-squash formal `push` run
[CI #43342455181](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43342455181)
is monitored separately; it is NOT pre-certified here.
Its completion receipt must be appended following actual completion.

Pinned Lean v4.30.0-rc2, mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
No Wilson/Haar/ZW source, root, workflow, assumptions or pins changed.
append-only / tighten-only / overwrite-forbidden / same-root.

## Open boundaries

H<=18 budget/top residual strict negativity versus equality remains NO_DATA.
The actual negative Haar-region mass r_H has no numerical certificate.
H>=19, H-uniform GL Rayleigh, Hamiltonian gap and the continuum 4D
Yang--Mills mass gap are unproved. Original AJA no-witness must never
be identified with a physical mass-gap theorem.

Proof record on canonical formal; any docs-only main mirror must
preserve this record's Git blob byte-identically and append
README/ROADMAP without overwriting prior text.


## Independently authenticated canonical formal-push receipt (2026-11-13 JST)

After the above pre-completion record, the independently triggered actual canonical squash [formal push CI #43342455181](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43342455181) has now completed **SUCCESS**, targeting exact canonical HEAD `da81af5042b1dcab219912423d966c982ef0c351`, `event=push`, run attempt 1. Its Changed Lean fast check built **11,457/11,457**, and all twelve AKV declarations have only the standard three axioms (`propext`, `Classical.choice`, `Quot.sound`); no `sorryAx`, AKV warning/error 0/0.

Independent completion receipt job `131616632898` completed **SUCCESS** and logged `event=push; exact_sha=da81af5042b1dcab219912423d966c982ef0c351; source_result=success; run=43342455181; attempt=1`. Combined GitHub commit status reports `success` for `chatgpt-ci-receipt/PR Lean Fast Check`. Actual canonical tree `6878c4853cc8e790a96c7b437998b386be4178de` matches authenticated source/test-merge/squash tree. The earlier monitored/pending statement is preserved as a historical pre-completion observation.

No stronger inference is licensed: only original H<=18 strict finite-power AJA witness nonexistence and B_H<=||Qf0_H||²/Delta_H<=0 are certified. Strict negativity versus equality, exact numerical Haar masses, H>=19, H-uniform GL Rayleigh, Hamiltonian and continuum Yang--Mills mass gap remain OPEN/NO_DATA.
