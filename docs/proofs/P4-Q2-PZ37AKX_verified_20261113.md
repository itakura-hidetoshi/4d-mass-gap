# P4-Q2-PZ37AKX — exact original H22 genuine Haar-mass conditional threshold

Date: 2026-11-13 JST.
Authoritative Lean theorem branch:
`formal/real-hilbert-uniform-coercive-strong-limit`.

## Scope: ORIGINAL model, strict condition, NOT measured Haar mass

Preserve original finite SU(2) Wilson physical transfer operator P,
normalized S=P/||P||, signed centered ZW source f0_H, the actual
product Haar measure mu_H, original normalized transfer u_H,
unchanged AIG margin m_H, original full-top orthogonal projection Q,
and the strictly defined original AJA budget

```text
B_(H,beta0) = m_(H,beta0)^2 * mu_H{A:u_(H,beta0)(A)<-m_(H,beta0)}
beta0 = log(3/2)/64
p_H = 24*(H+1)^3.
```

The previously certified AKW result is a TRUE SU(2) Haar single-link
partition estimate, not an assumed Gaussian law:

```text
Z_H(beta0) <= exp(-beta0*p_H)*exp((44/351)*beta0²*p_H).
```

AKX retains the actual negative-region Haar mass
`r_H=mu_H{u_H<-m_H}` in the partition-Haar test and proves:

```text
r_H * exp((44/351)*beta0²*p_H) <= 4
  => r_H*Z_H(beta0) <= 4*exp(-beta0*p_H)
  => no original strict finite-power AJA witness
  => B_(H,beta0) <= ||Q_(H,beta0) f0_H||²
  => Delta_H := B_(H,beta0)-||Q f0_H||² <= 0.
```

The last three lines are two separate consequences of the SAME
sufficient condition, not a claim that an AJA no-witness by itself
proves a top-residual inequality.

For H=22 the exact original p_22=292008 is certified, giving the
explicit original-measure conditional threshold:

```text
r_22 <= 4*exp(-(44/351)*beta0²*292008)
```

which, if independently established for the actual Haar-negative
region, excludes original H22 AJA strict finite-power witnesses,
establishes B_22<=||Q f0_22||² and Delta_22<=0.
The threshold evaluates approximately to 0.9204180158, but
**that decimal is a mathematical evaluation of a condition,
not an actual measured or certified r_22 numerical upper bound**.
No new r_22 datum has been supplied. H22 unconditional no-witness
and unconditional Delta_22<=0 remain NO_DATA.

## Lean source, imports and exact-source authentication

New append-only module:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalH22GenuineHaarThresholdV5_PZ37AKX.lean`.

Nine new declarations, each with a matching `#print axioms`:
1. `p4Q2PZ37AKX_originalFixedCoupling_partitionHaarMass_of_sharpThreshold`
2. `p4Q2PZ37AKX_originalFixedCoupling_no_AJA_of_sharpThreshold`
3. `p4Q2PZ37AKX_originalFixedCoupling_budget_le_top_of_sharpThreshold`
4. `p4Q2PZ37AKX_originalFixedCoupling_delta_nonpos_of_sharpThreshold`
5. `p4Q2PZ37AKX_originalH22_plaquetteCount_exact`
6. `p4Q2PZ37AKX_originalH22_sharpThreshold_to_massFactor`
7. `p4Q2PZ37AKX_originalH22_no_AJA_of_genuineHaarMass`
8. `p4Q2PZ37AKX_originalH22_budget_le_top_of_genuineHaarMass`
9. `p4Q2PZ37AKX_originalH22_delta_nonpos_of_genuineHaarMass`

[AKX theorem PR #6718](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6718)
**MERGED** onto the original canonical formal branch.
Authenticated exact-source commit
`90eb68e7c3662d3dfa85dc1eefe4093f18dd4654`.
Canonical theorem squash
`ee5f4f91a72ee01bb859420df5eb4c5022db1ccd`.
Source/test-merge/squash common Git tree:
`d48502479e8c5089a88246fd6182f4c48f6c9c88`.

[Exact-source CI #43364965116](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43364965116)
completed/**SUCCESS**, pinned Lean **11,459/11,459**,
9/9 new declarations report only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
New sorryAx absent; AKX changed-file warning/error 0/0.
Independent exact-head PR completion receipt job
`131689536145` completed/SUCCESS, source result `success`
and GitHub commit status `success`.

Independently triggered canonical formal-squash
[push CI #43365907391](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43365907391)
is monitored separately. Do **NOT** treat it as certified until
completed/SUCCESS with exact-head completion receipt.
Append that receipt as later provenance, preserving this statement.

Lean v4.30.0-rc2 and pinned mathlib
`5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
New Lean module only; existing physical/operator/source/Haar/top
definitions, existing Lean files, roots, assumptions, workflows
and dependency pins unchanged. append-only/tighten-only/
overwrite-forbidden/same-root.

## Remaining obstruction and next physical task

Independently certify genuine r_22 <= exact threshold, e.g.
through actual original Haar complementary Borel cells with
valid pointwise original transfer floors and mass certificates.
The earlier AKR H14 finite Borel-cell descent is a methodological
reference, NOT an H22 certified mass table.
Alternatively establish stronger genuine transfer/operator estimates
without changing the model.

Strict Delta_H<0 versus equality, H>=23, H-uniform GL Rayleigh
coercivity, Hamiltonian spectral gap and continuum 4D
Yang–Mills mass gap remain OPEN. Conditional H22 AJA no-witness
is NOT the physical spectral gap or a continuum mass-gap proof.

Any docs-only main mirror must preserve this proof record's
identical Git blob and append README/ROADMAP without overwrites.


## Independent canonical formal-push certification (2026-11-13 JST)

The earlier monitored/unverified push description above is preserved as a historical snapshot. The actual independently triggered canonical formal squash [push CI #43365907391](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43365907391), exact integrated HEAD `ee5f4f91a72ee01bb859420df5eb4c5022db1ccd`, event `push`, run attempt 1, has completed **SUCCESS**. Changed Lean fast check job `131690160600` built **11,459/11,459** and independently printed all 9 AKX declarations' axioms: only `propext`, `Classical.choice`, `Quot.sound`; no new `sorryAx`, AKX warning/error 0/0.

The exact-head completion receipt job `131692258724` completed **SUCCESS** and recorded `event=push; exact_sha=ee5f4f91a72ee01bb859420df5eb4c5022db1ccd; source_result=success; run=43365907391; attempt=1`. GitHub combined status reports `success` in `chatgpt-ci-receipt/PR Lean Fast Check`. The actual canonical squash tree `d48502479e8c5089a88246fd6182f4c48f6c9c88` is identical to the authenticated theorem source/test-merge tree.

This independent receipt verifies ONLY the already certified **conditional** H22 original Haar mass threshold theorems. It supplies no numerical bound on actual r22, no unconditional H22 no-witness, no strict Delta22 sign/equality, no H-uniform Rayleigh, and no Hamiltonian or continuum Yang–Mills mass gap.
