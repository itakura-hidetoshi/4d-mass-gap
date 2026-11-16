# P4-Q2-PZ37AMG — actual SU(2) Wilson finite-volume Gibbs plaquette covariance geometric decay at original beta0

Date: 2026-11-16 JST. Theorem [PR #6788](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6788) **MERGED** into authoritative Formal `formal/real-hilbert-uniform-coercive-strong-limit` as exact two-parent canonical theorem commit `6b48eabefc06aeeb7e508745167d598693ab0135`.

## New physical statement and exact ancestry

AMF #6785 previously proved that the exact original Wilson `SU(2)` coupling
`beta0 = log(3/2)/64` obeys `0 < beta0 < log(19/17)/4` and that the
true compact-Haar Gibbs conditional-link Dobrushin coefficient is strictly
subunit. AMG uses this fixed beta0, **not a new tuned/surrogate coupling**.

The existing module `PeriodicHypercubicEvenFiniteSupportGibbsCovarianceSpatialGeometric.lean` already proves a nontrivial **finite-volume interacting compact SU(N) Wilson Gibbs covariance** geometric bound for bounded-continuous observables supported on physically plaquette-locally separated finite link sets. AMG explicitly **inherits** this existing finite-volume random-scan/Gibbs covariance theorem and supplies its missing physical-specialization interface; AMG does not falsely attribute the generic covariance theorem to this new PR.

One new append-only 327-line Lean file:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0PhysicalPlaquetteGibbsCovarianceV5_PZ37AMG.lean`.

AMG makes the active conditional-TV scalar `q(beta) = (exp(4beta)-1)/(exp(4beta)+1)` definitionally equal to AMF's actual compact-Haar `eta(beta)`, discharging the existing covariance theorem's strict `18q(beta0)<1` hypothesis **for the ORIGINAL beta0**. Then it constructs the fundamental character `chi = 1-E` of an ACTUAL oriented four-edge physical periodic `SU(2)` plaquette, as a bounded-continuous function on the **FULL interacting Wilson configuration**. Link-support dependence is certified by equality on the four real positive boundary edges, without an independence approximation or synthetic kernel.

The genuine physical Wilson energy satisfies `0<=E<=2`. AMG proves `||chi_p||_infty<=1`, that any physical plaquette uses at most 4 links, and thus each finite-link variation prefactor is at most `2*4*1=8`.

Let `mu_{H,beta0}` be the genuine finite-volume original `SU(2)` Wilson Gibbs law with all interacting plaquettes. For **each H>0**, and each pair of ACTUAL oriented plaquettes `p,q` whose physical four-edge support sets satisfy the already-verified typed `periodicHypercubicEvenSupportsPlaquetteLocalSeparatedBy H D S T` hypothesis, the final theorem proves the EXACT explicit estimate

```text
rho0 = 18 * (exp(4*beta0)-1)/(exp(4*beta0)+1)
0 <= rho0 < 1,

|Cov_{mu_{H,beta0}}(chi_p,chi_q)|
  <= 64 * rho0^D / (1-rho0).
```

Here `Cov` is the centered correlation in the **full interacting original Gibbs measure**, with no separate independent plaquette law and no replacement of the original full Wilson partition function. Both the geometric rate `rho0` and the numerical prefactor `64/(1-rho0)` are independent of H. The statement is conditional only on the actual SUPPORT SEPARATION of the selected plaquettes, not on an unproved covariance inequality: the generic covariance comparison was already mechanically established in the repository.

**Critical obstructions retained:** neighboring physical plaquettes (in particular AME's shared-link pair) have overlapping link supports, so there is **no proof that their separation D is positive**; only `D=0` is immediate there. The existing n>=3 shared-plaquette uniqueness used for the estimate restricts this AMG theorem to `H>0`; `H=0` (length n=2) needs independent degenerate-torus treatment. The theorem is finite-volume and fixed beta0; it does not establish the factorial weak-coupling/continuum scaling of beta, Gauss-law Hilbert-sector compatible cross-H OS transfer comparison, Hamiltonian spectral gap, or continuous 4D Yang-Mills mass gap. **Preference/conditional covariance decay is NOT authority for those global statements.**

## Twelve verified declarations

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`, all prefixed `p4Q2PZ37AMG_`:

1. `originalFixedBeta0ActiveTVMajorant_eq_eta`
2. `originalFixedBeta0ActiveTVMajorant_strict`
3. `originalFixedBeta0System`
4. `originalPhysicalPlaquetteCharacterBCF`
5. `originalPhysicalPlaquetteCharacterBCF_apply`
6. `originalPhysicalPlaquetteCharacterBCF_eq_of_eqOn_edges`
7. `originalFixedBeta0GibbsCovariance_geometric_finiteSupport`
8. `originalFixedBeta0PhysicalPlaquetteGibbsCovariance_geometric`
9. `originalPhysicalPlaquetteCharacterBCF_norm_le_one`
10. `originalPhysicalPlaquetteEdgeSupport_card_le_four`
11. `originalPhysicalPlaquetteCharacterVariationSum_le_eight`
12. `originalFixedBeta0PhysicalPlaquetteGibbsCovariance_abs_le_explicit`

## Version-bound source and proof-only repair / strengthen record

- Parent authoritative Formal before AMG: `d10fe1a69297a010f0ac803b80defa9bf7707652` (AMF theorem/official record). No previous Lean source, pinned toolchain, original Wilson action, Haar, fixed beta0, AJA/Gauss, transfer operator or root modified.
- Initial source `a3c9597092269c2c8a0e79cc4569e70ef071c61d` had the original `p4Q2PZ35C_originalOneLinkCharacter` referred to through a wrong nested Lean namespace. The [CI #43793544193](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43793544193) was **cancelled** on source update, NOT classified as a completed failed Lean proof.
- Corrected head `ef73cb7a8a265b6fa7f034d392c424bf1af5d07e`: [CI #43793693508](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43793693508) **completed/SUCCESS**, pinned Lean `11,510/11,510`, eight public declarations only the standard three axioms, no `sorryAx`. The new file still had three unused-sum-binder LINTER warnings. That source is not the final accepted exact source.
- Final strengthened proof `b0dfef7bac142b1a52fd1f9c19cdf8f5a8fcb080` renames those bound variables and adds four NEW substantive theorems: physical character sup norm ≤1, four-edge support cardinality ≤4, variation sum ≤8, and the explicit uniform prefactor **64**. This is tighten-only: original theorem statements are not weakened.
- [Exact-source PR CI #43794645216](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43794645216) **workflow/Lean job/required Lean step/independent receipt completed/SUCCESS**, exact repaired-and-strengthened HEAD `b0dfef7bac142b1a52fd1f9c19cdf8f5a8fcb080`. Pinned Lean v4.30.0-rc2 / mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`: **11,510/11,510** dependency check SUCCESS; full **12/12** `#print axioms` only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`; AMG warnings/errors **0/0**. Main Lean job `133060563312` and independent exact-HEAD receipt job `133062162321` both completed/SUCCESS.
- Exact receipt: `event=pull_request exact_sha=b0dfef7bac142b1a52fd1f9c19cdf8f5a8fcb080 source_result=success run=43794645216 attempt=1`.
- Source `b0dfef7bac142b1a52fd1f9c19cdf8f5a8fcb080`, synthetic GitHub test-merge `c590c45a4d58c60532fd03cbcc037a49e1a3e002`, and actual two-parent Formal theorem merge `6b48eabefc06aeeb7e508745167d598693ab0135` all share **Git tree `a91ceb217a4028324c01efbc1d49ee49764f66d1`**, with actual merge parents `d10fe1a69297a010f0ac803b80defa9bf7707652` and the exact final source `b0dfef7bac142b1a52fd1f9c19cdf8f5a8fcb080`.
- Independent [canonical event=push CI #43795226737](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43795226737) on **integrated theorem HEAD** `6b48eabefc06aeeb7e508745167d598693ab0135` was observed `in_progress` initially. Do **NOT** promote this pending historical observation to postmerge success before separately auditing actual workflow/job/step and receipt. Append later real result separately.

**CodeAI / standalone Lean MCP execution receipt:** NO_DATA in this session; the verified checker is pinned GitHub Actions, without an assertion that an unavailable agent or service ran.

## Next research target — AMH / scale and physical bridge

Make actual selected p,q separation quantitative in physical Euclidean coordinates and prove shell-count summability of this finite-volume fixed-beta0 bound. Then investigate whether the same beta0 region can be reconciled with physical continuum coupling sequences (which may not remain small). Independently construct the Gauss-law compatible OS one-slab transfer / Hilbert carrier comparison needed before any all-H physical transfer gap and Hamiltonian spectral promotion.

The AME adjacent shared-link case, H=0 degenerate case, independent physical continuum Yang–Mills reconstruction, and all-H beta0 transfer/Hamiltonian/4D continuum mass gap are still **OPEN/NO_DATA**, notwithstanding AMG's verified finite-volume connected Gibbs plaquette clustering conditional on actual support separation.


## Independent canonical postmerge push authentication — 2026-11-16 JST

The preceding historical `in_progress` observation for the actual theorem-merge [push CI #43795226737](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43795226737) is preserved rather than retroactively rewritten. GitHub MCP independently reobserved `event=push` on the **actual exact integrated Formal theorem HEAD `6b48eabefc06aeeb7e508745167d598693ab0135`**, and workflow **completed/SUCCESS**. Main changed-Lean job `133062412337`, required `Run changed Lean fast check` step, and independent receipt job `133064594630` all **completed/SUCCESS**. The genuine pinned dependency closure was **11,510/11,510**; the exact AMG source's 12/12 `#print axioms` commands used only `propext` / `Classical.choice` / `Quot.sound`, **no sorryAx**, AMG warning/error **0/0**. Actual canonical tree remains `a91ceb217a4028324c01efbc1d49ee49764f66d1`, identical to the source and test-merge trees.

Independently emitted exact-HEAD receipt:

```text
event=push exact_sha=6b48eabefc06aeeb7e508745167d598693ab0135 source_result=success run=43795226737 attempt=1
```

This is a formal validation of **finite-volume fixed-beta0 interacting SU2 Gibbs covariance geometric decay conditional on real physical-link separation**, not a theorem of all-H physical OS transfer, Hamiltonian spectral, or continuum four-dimensional Yang-Mills mass gap.
