# P4-Q2-PZ37AMI — actual SU(2) Wilson physical plaquette incidence and finite Green L¹ budget

Date: 2026-11-16 JST.

## Certified antecedent, canonical source and physics

- Authoritative Formal branch: `formal/real-hilbert-uniform-coercive-strong-limit`; original coupling `beta0=log(3/2)/64`.
- The preceding true full interacting Wilson Gibbs plaquette connected-correlation theorem [AMG #6788](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6788) and its physical-time specialization [AMH #6791](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6791) are already merged and preserved.
- [AMI theorem PR #6794](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6794) **MERGED** as canonical two-parent Formal commit `8194a5d107cbb4e2477457c9b6115da851c49374`, with exact source parent `c790585f058014b6a1f6402c1af0373865eaef5a` and previous Formal parent `3ae06f27ae62d9bc6ce7e22c162d33e03f5f00f7`.
- New 256-line append-only Lean file `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0PlaquetteIncidenceGreenL1V5_PZ37AMI.lean`, six declarations and six #print axioms. No preexisting Wilson action, compact Haar, Gauss-law, AJA, AMF/AMG/AMH, original physical transfer carrier, Lean/mathlib pins, workflows or same-root structure modified.
- Pinned Lean `v4.30.0-rc2`, mathlib `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.

## Physically exact finite-volume statements

For each even-periodic four-dimensional physical Wilson SU(2) lattice of side length `2(H+1)`, actual physical oriented plaquette `p`, and positive-link `e`:

```text
e in the four real positive physical boundary links of p
  IFF p belongs to the canonical touching-plaquette incidence set at e.

number of actual coordinate plaquettes touching e <= 6
sum over all physical plaquettes p of
  (if e belongs to physical support(p) then 2 else 0) <= 12

chi_p(A) = 1 - SU2_Wilson_Plaquette_Energy(holonomy(A,p))
||chi_p||_sup <= 1
sum over all ACTUAL plaquettes p of coarse one-link variation at e <= 12.
```

For `H>0`, `beta0=log(3/2)/64`, and true compact-Haar conditional-law Dobrushin coefficient `rho0=18*(exp(4*beta0)-1)/(exp(4*beta0)+1)` with `0<=rho0<1`, define `w_{p,M}` as the **actual compact SU(2) Wilson finite random-scan accumulated Dobrushin link-variation profile** of the character `chi_p`. The sixth theorem proves the uniform bound

```text
for every H>0, actual p, and M>=0:
  sum over all physical positive links e of w_{p,M}(e)
     <= 8 * (1-rho0)^(-1).
```

The bound is uniform in H and M, and preserves the original interacting Wilson physical system, not a surrogate independent plaquette measure. It is a finite **Green-resolvent L¹ link-variation statement**, not yet a bound on the SUM of absolute Gibbs connected covariances. A further finite-family covariance telescope and finite-sum limit proof is needed.

## Six Lean theorems

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`:

1. `p4Q2PZ37AMI_originalPlaquetteEdgeSupport_mem_iff_touches`
2. `p4Q2PZ37AMI_originalPlaquettesContainingLink_eq_touching`
3. `p4Q2PZ37AMI_originalPlaquettesContainingLink_card_le_six`
4. `p4Q2PZ37AMI_originalPlaquetteUnitOscillationSum_le_twelve`
5. `p4Q2PZ37AMI_originalPlaquetteCharacterVariationAtLink_sum_le_twelve`
6. `p4Q2PZ37AMI_originalPhysicalPlaquetteRandomScanGreenL1_le_eight`

## Version-bound source repair and independent CI evidence

- First candidate source `b669d4d917d3d860520c39b5d7e391a0f2e3f301` then exact argument-order repair `d835c110b8e9999c3ec2bc400e5704621a4ee746`. [CI #43824437268](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43824437268) Lean step FAILURE: 3 direct source diagnostics. A `simp only` invocation had already discharged the goal, so a following `constructor` reported “No goals to be solved”; `simp` unfolded the side-length through an incidental positive-half slab expression, so `omega` could not recover the actual `3 <= 2*(H+1)` relation; the centered finite-support profile was elaborated without a fixed `C` compact gauge system.
- Repair source `25b7928596d01d57da21c044cd8687fb78434650`, [CI #43825229811](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43825229811) Lean step FAILURE with 2 remaining *type-inference* errors at applications of centered profile support/variation lemmas. The five physical incidence and oscillation declarations had standard-three-only axiom output, but the sixth declaration reported `sorryAx` while its proof failed. This intermediate failure is NOT a certified theorem.
- Final corrected exact source `c790585f058014b6a1f6402c1af0373865eaef5a` uses explicit `(C:=C)`, `(e:=e)` at the relevant imported lemmas; retains the original mathematical statements without weakening H, incidence, coupling, Gibbs data or any other assumptions.
- [Exact-source CI #43825859327](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43825859327) workflow, main changed-Lean job `133159445011`, required Lean step and independent exact-SHA receipt job `133161295404` all completed/SUCCESS. **11,512/11,512** dependency-aware pinned Lean build, all **six/six** `#print axioms` only `propext` / `Classical.choice` / `Quot.sound`, **no sorryAx**, direct AMI warning/error **0/0**.
- Independent receipt: `event=pull_request exact_sha=c790585f058014b6a1f6402c1af0373865eaef5a source_result=success run=43825859327 attempt=1`.
- Source, GitHub test-merge commit `466b2dd2b429704013d33bc48b7e649f6670696b`, and canonical Formal theorem merge `8194a5d107cbb4e2477457c9b6115da851c49374` share exactly **Git tree `a5ea3dad73c570aead556492f1fc60202eff1888`**.
- Canonical integrated event=push [CI #43826552529](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43826552529) was **in_progress** when this historical record was first authored. Do NOT promote it to independently certified until separately inspecting the exact SHA, workflow, Lean job and step, full axiom output and independent push completion receipt. Append its later observation without rewriting this entry.

## Next mathematical target and retained obstructions

The next theorem must combine the already established true compact Gibbs finite random-scan covariance telescope with (i) the sum over real physical plaquettes of one-link character variation ≤12, (ii) the actual fixed-plaquette resolvent L¹ bound ≤8/(1-rho0), and (iii) finite-sum interchange/convergence of the vanishing random-scan covariance remainder. This should provide, **if successfully proved and checked**, an H-uniform absolute Gibbs plaquette covariance-sum upper bound `96/(1-rho0)`. It is a target, not an existing certified AMI result.

Do not confuse this linkwise resolvent with OS temporal transfer or Hamiltonian spectrum. The old exponential `24^D` shell bound cannot yield sum convergence at beta0 because `24*rho0>1`. Full four-coordinate Euclidean physical distance with polynomial shell counting, an all-H physical Gauss-law-compatible OS transfer, continuum scaling `beta(H)`, Hamiltonian spectral gap and four-dimensional continuum Yang–Mills mass gap remain OPEN/NO_DATA. H=0 remains outside the strict n>=3 Gibbs uniqueness route.

Independent KuuOS CodeAI/standalone Lean MCP execution receipt: **NO_DATA**. Exact-source and canonical proofs here are checked by pinned GitHub Actions Lean; no execution authority is assigned to an unobserved CodeAI run.
