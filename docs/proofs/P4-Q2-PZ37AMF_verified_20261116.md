# P4-Q2-PZ37AMF — original SU(2) Wilson fixed-beta0 strict physical-link Dobrushin certificate

Date: 2026-11-16 JST. AMF theorem [PR #6785](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/6785) **MERGED** into authoritative `formal/real-hilbert-uniform-coercive-strong-limit` as canonical two-parent commit `73b1c310f34f9158957dc942988cc30613215e3c`.

## Actual mathematical theorem and scope

One new append-only 224-line Lean leaf:
`MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2OriginalFixedBeta0SharedLinkDobrushinInfluenceV5_PZ37AMF.lean`.

The authentic Wilson SU(2) periodic four-dimensional lattice uses the **unchanged** fixed coupling `beta0 = log(3/2)/64` from ADC, and true compact-Haar single-link conditional distributions under the **full interacting finite-volume Wilson Gibbs law**, never a product Gibbs law.

Existing AKO certifies `beta0 <= 1/156`. AMF proves a separate rational logarithmic bound `2/19 <= log(19/17)`, then identifies the original fixed beta0 as strictly below the existing **genuine non-Abelian SU(N) compact-Haar Dobrushin threshold**:

```text
0 < beta0 < log(19/17)/4.
alpha0 = 18 * periodicHypercubicSpecialUnitaryDobrushinEta beta0
       = 18 * (exp(4*beta0)-1)/(exp(4*beta0)+1) < 1.
```

For every positive half extent `H>0`, `n=2(H+1)>=4`, the existing physical periodic SU(2) Wilson single-link conditional influence matrix is **constructed**, with coefficient `alpha0` independent of `H`. Each physical target-link row has sum strictly below one, and the true conditional Gibbs expectations obey a bounded-test TV-duality difference estimate when backgrounds differ at one physical source link:

```text
|E[phi(U_target) | background A] - E[phi(U_target) | background B]|
    <= 2 * C_{target,source},
   |phi(g)| <= 1,  A and B agree away from source.
```

The same original influence matrix has an `ell^2` nonexpansive action by the **existing certified finite Schur inequality**. AMF finally applies its strict row estimate to a concrete physical edge shared by the two DISTINCT primary spatial plaquettes from AME #6782. This last bridge does not assert that plaquette observables are independent.

The `H=0` case is intentionally **not claimed**: the original shared-plaquette uniqueness result supplying the compact physical row bound is stated only for `n>=3`, whereas `H=0` has periodic length two. This is an explicit typed obstruction, not a reason to silently weaken the existing geometry or change the original lattice.

## Critical physical distinction and unproved layer

A Dobrushin **single-link conditional-law** contraction is NOT by itself a theorem about the **joint connected covariance** `Cov_Gibbs(chi_p,chi_q)` for real SU(2) Wilson plaquettes. The full finite conditional-to-joint-covariance comparison/coupling or random-scan telescoping bound is still required. In particular a uniform physical OS transfer gap or Hamiltonian/continuum mass gap cannot be promoted from this local certificate. A centered random-scan `L^2` Rayleigh comparison field exists in older conditional certificate structures, and AMF neither assumes it nor proves it. No false use of `H=0`, no extra physics axioms or surrogate Wilson kernel.

## Eight declarations and exact pinned axiom audit

Namespace `MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint`, prefix `p4Q2PZ37AMF_`:

1. `log_nineteenSeventeenths_ge_twoNineteenths`
2. `originalFixedBeta0_lt_DobrushinThreshold`
3. `originalFixedBeta0_DobrushinCoefficient_lt_one`
4. `originalFixedBeta0PhysicalDobrushinMatrix`
5. `originalFixedBeta0PhysicalInfluence_rowSum_lt_one`
6. `originalFixedBeta0PhysicalConditionalIntegral_abs_le`
7. `originalFixedBeta0PhysicalInfluence_l2_nonexpansive`
8. `originalPrimaryNeighbor_sharedEdge_strictInfluence`

## Failure -> repair -> independent exact-source proof

- Baseline authoritative Formal HEAD `5fae2dbcce01b372c395f4fa423b30fad721e071`, main then `9c9ba3dceaa569032dee757268bc49ed62c80b31`.
- Initial AMF source HEAD `5233ffa9a51d154aeaaceb7718e896be3dff9229`. Exact source [CI #43782230120](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43782230120) **FAILED** at two direct Lean errors: line 126 lacked a local `MeasurableSpace` for actual compact SU(2) gauge group `G` when checking the bounded-test conditional integral; line 163 `positivity` could not infer positivity of the named original fixed beta0 inside the Schur proof. Initial elaboration recovery displayed `sorryAx` on those unfinished declarations; initial FAILED source must never be considered certified.
- Proof-only repaired source HEAD `a154dc732b959f248d6f7ab9ee03d7fd9a5ebf07` supplies the canonical existing `specialUnitaryGroupMeasurableSpace 2` instance and explicitly applies existing `p4Q2PZ37ADC_fixedCoupling_pos` via `mul_nonneg`. **No theorem signatures, hypotheses, Wilson action, original beta0, Haar, AJA/Gauss, dependency pins or public root altered.**
- [Exact-source pinned Lean CI #43782877096](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43782877096) **workflow completed/SUCCESS** at exact repaired HEAD `a154dc732b959f248d6f7ab9ee03d7fd9a5ebf07`. Real pinned dependency build **11,467/11,467 SUCCESS**; 8/8 declared `#print axioms` uses only `propext`, `Classical.choice`, `Quot.sound`; no new `sorryAx` and AMF changed-file warning/error **0/0**. Main changed-Lean job `133023844863` and independent receipt job `133025340941` both completed/SUCCESS. Exact emitted receipt `event=pull_request exact_sha=a154dc732b959f248d6f7ab9ee03d7fd9a5ebf07 source_result=success run=43782877096 attempt=1`.
- Exact repaired source, GitHub PR synthetic test-merge commit `7ca900c53947044f833cbc68e2a49894cbb1f79b`, and actual canonical theorem merge `73b1c310f34f9158957dc942988cc30613215e3c` all share **Git tree `ac2ed3e62e3e82d021b3db620802b2b873116c01`**. The actual canonical theorem merge has parents `5fae2dbcce01b372c395f4fa423b30fad721e071` and `a154dc732b959f248d6f7ab9ee03d7fd9a5ebf07`.
- Independent [postmerge canonical event=push CI #43783428357](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43783428357) on **actual theorem merge HEAD `73b1c310f34f9158957dc942988cc30613215e3c`** was observed **in_progress**. This is a historical pending observation, NOT an independent push success claim. Append its actual result only after full workflow/job/Lean step and completion receipt are independently verified.

**CodeAI/standalone Lean MCP execution receipt:** NO_DATA in this GitHub-MCP session. The actual check is the pinned GitHub Actions Lean process.

## Next mathematical obstruction (AMG)

Derive the missing conditional-law-to-joint-observable **Gibbs covariance comparison** from genuine Wilson conditional distributions and their Dobrushin matrix. Need to preserve the true shared-link dependencies for adjacent plaquettes and then prove explicit decaying link-influence Green-tail estimates for separated physical plaquette supports. Prove volume-independent cluster summability and Gauss-law/physical transfer compatibility before any gap claim. Nontrivial `Cov_Gibbs(chi_p,chi_q)` decay, all-H beta0 transfer gap, Hamiltonian gap and continuum four-dimensional Yang-Mills mass gap remain OPEN/NO_DATA.


## Independent canonical postmerge push certification — 2026-11-16 JST

The earlier *in_progress* observation for [actual canonical event=push CI #43783428357](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/43783428357) remains in the record as historical. Independent GitHub MCP reobservation now verifies the **actual two-parent AMF theorem canonical HEAD `73b1c310f34f9158957dc942988cc30613215e3c`** with **workflow completed/SUCCESS**, main changed-Lean job `133025628213`, required `Run changed Lean fast check` step, and independent receipt job `133027681892` all **completed/SUCCESS**. Pinned Lean full dependency closure **11,467/11,467 SUCCESS**, eight AMF `#print axioms` only `propext` / `Classical.choice` / `Quot.sound`, no `sorryAx`, AMF changed-file warning/error **0/0**. Source/test-merge/canonical Git tree `ac2ed3e62e3e82d021b3db620802b2b873116c01` is exact.

Actual independent receipt:

```text
event=push exact_sha=73b1c310f34f9158957dc942988cc30613215e3c source_result=success run=43783428357 attempt=1
```

This verifies the original SU2 Wilson local fixed-beta0 Dobrushin influence theorem at the integrated HEAD, NOT a new Gibbs plaquette connected-covariance decay theorem, transfer gap or continuum Yang-Mills mass gap.
