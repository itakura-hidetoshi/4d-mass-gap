# MGAP4D — Formalization Roadmap

**Status: 2026-10-09 JST. Last verified theorem-bearing merge: [PR #5326](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5326), `ae59199bb6b4a1a6d3afb31f3e9b5fb2a411727c`.**

**Current program:** close physical **P4-Q2 volume dependence for the actual original SU(2) Wilson uncentered right-Krylov Gram**, then carry the proved controls into the independent adjacent-scale and continuum obligations. **P4-F1/F2/F3 are CLOSED, P4-Q1 is CLOSED quantitatively at fixed finite volume, and P4-Q2 is proved through a constructed physical linkwise Rayleigh bound.** Neither an H-uniform estimate nor a continuum four-dimensional Yang–Mills mass gap has been established.

Read [README.md](README.md) for theorem definitions, precise finite-volume inequalities and a minimal active source chain.

## 0. Authority, environment and evidence

| Item | Value |
| --- | --- |
| Unique theorem-bearing repository/branch | `itakura-hidetoshi/4d-mass-gap` / `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest validated theorem-bearing merge | **#5326** · `ae59199bb6b4a1a6d3afb31f3e9b5fb2a411727c` |
| PR #5326 head | `6677af987415248a619039b32138a663aaf31210` |
| Pinned Lean | `leanprover/lean4:v4.30.0-rc2` |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact PR-head Lean Fast Check | [37910157743](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37910157743) — **SUCCESS** |
| Changed Lean job / MCP completion receipt | `113753105635` / `113754562387` — **SUCCESS / SUCCESS** |
| Exact build / changed-file warnings and errors | **10,426 / 10,426**; **0 / 0**; no new `sorry` / `admit` / `axiom` |

Before a new PR, reobserve the **fresh exact authoritative branch HEAD**; treat that SHA and its Lean artifacts as first authority. Then use docs, matching exact-head CI and historical handoffs, in that order. The default GitHub `main` is **not** theorem authority. Docs-only updates move the authoritative branch HEAD but do not supersede the latest theorem-bearing merge.

## 1. Proof-status matrix (never conflate these gates)

| Lane | Formal closure now in the authoritative branch | Remaining mathematical work |
| --- | --- | --- |
| **P4-F1** | **CLOSED** (#5299): original pair-Haar a.e. equality lifted to all four crossed Wilson density entries; strictly positive original fourfold minor event | No further F1 gate before fixed-volume strictness |
| **P4-F2** | **CLOSED** (#5300–#5301): actual right-link fiber obstruction descends to the original retained sigma algebra | Do not re-open without finding a genuine error in formal assumptions |
| **P4-F3** | **CLOSED** (#5302): true original positive-`beta` posterior vacuum `E_vac(beta,H) > 0` for every fixed finite H | A bound **uniform in H/beta** is a different problem |
| **P4-Q1** | **Finite-H quantitative closure** (#5303–#5309): original retained `L²` witnesses; `E_vac <= |E_H|(exp(16 beta)-1)^2` | Remove or genuinely control `|E_H|` without inventing a product measure/support hypothesis; still OPEN |
| **P4-Q2 (orthogonal)** | #5310–#5314: authentic physical orthogonal receiver `O_H(beta)` / `O_H(beta²)`, explicit distinct fine/frozen beta bounds, centered Gram | Global action budget `B_H` and vacuum-floor `m_H(beta)^(-1)` remain H-dependent |
| **P4-Q2 (uncentered)** | #5315–#5319: genuine vacuum/excitation decomposition; explicit finite-H unit receiver and two-beta coefficient-ℓ¹ Rayleigh bound | Do not mistake coefficient-ℓ¹ for uniform ℓ² |
| **P4-Q2 (signed posterior)** | #5320–#5324: exact link residuals, signed mode covariance, original `CondExpL2` covariance/fiber cross-integral, two-copy polarization and exact Gram = half actual resampling energy | Bound **signed covariance rows** using physically proved locality, not an asserted Schur hypothesis |
| **P4-Q2 (constructed link budgets)** | **#5325–#5326**: authentic posterior resampling controlled by physical BCF right-link oscillation; explicit `W × M_F` half-density/mean sup-norm link coefficient | Prove useful, preferably H-uniform, summability and operator-norm control. **ACTIVE** |
| C1/C2/C3 | Earlier adjacent-scale interfaces and conditional results | Common-marginal physicality, vector-wise reconstruction/transfer compatibility, weighted beta-trajectory summability — **OPEN** |
| H2/H3/H4 | Finite-volume transfer, reconstruction and conditional spectral infrastructure | Spacing-scaled dynamics/generator; continuum OS Hamiltonian; Wightman Yang–Mills spectrum and positive mass gap — **OPEN** |

### What is now genuinely closed

The old README's assertion that a fourfold a.e. lift, single-right-link retained-sigma descent, and positive fixed-H vacuum energy remained open was **outdated after #5299–#5302**. The proved chain now is:

```text
original Wilson positive fourfold minor (#5296–#5297)
  -> four crossed original-law a.e. lift (#5299)
  -> original right-link fiber and retained-sigma descent (#5300–#5301)
  -> E_vac(beta,H) > 0, fixed finite H and beta>0 (#5302)
  -> original retained local Wilson L2 witnesses
     with E_vac(beta,H) <= |E_H|(exp(16 beta)-1)^2 (#5303–#5309).
```

A strictly positive number for each H can still converge to zero as H grows. The upper bound above grows with `|E_H|`. **Neither side supplies a positive continuum spectral mass gap.**

## 2. Current exact mathematical object: true uncentered right-Krylov Gram

At the actual finite spatial volume `H = halfExtent(n+1)`, distinguish:

- **Fine physical orbit:** `R_(n,j) = S_(beta_(n+1),H)^j u_H`, retaining the existing exact Krylov indexing and input definitions.
- **Frozen physical receiver and posterior:** `V_(beta_n)` and `Q_(beta_n,e) = U_(beta_n)^(-1) P_(beta_n,e) U_(beta_n)`, defined under the **original** Wilson joint law.
- **Original signed residual:** `r_(e,j) = (I-Q_(beta_n,e)) V_(beta_n)(R_(n,j))`.
- **True uncentered Gram:** `G_(i,j) = sum_e inner(r_(e,i),r_(e,j))`.

For a real coefficient family `a` and `F_a = sum_j a_j R_(n,j)`, **#5324** identifies without loss:

```text
a* G_right a
  = (1/2) * sum_e E_originalResampling(beta_n,e; F_a).
```

PRs #5321–#5323 identify `G_ij` with the **signed** link covariance of the actual original Wilson conditional expectation and its literal physical posterior-fiber integral. The finite Schur theorem is **conditional**: if a proved physical covariance row majorant satisfies `sum_j |G_ij| <= C` for all i, then `a*G_right a <= C sum_i a_i^2`. No H-independent C has been derived.

### Newest constructed original physical bound (#5326)

Write the exact existing full joint receiver

```text
V_joint(beta_n,F_a) = W_(beta_n) * M_(beta_n,F_a),
W_(beta_n)(A,B) = ||T_(beta_n)||^(-1) * Omega_(beta_n)(B)
                  / sqrt(rho_joint(beta_n;A,B)).
```

Define `delta_e X(z,g) = X(z) - X(z.1, update(z.2,e,g))` and its **actual** compact-carrier BCF supremum `osc_e(X)=||delta_e X||`. #5326 proves an unconditional, physically instantiated bound

```text
b_e(F_a)
  = ||W|| * osc_e(M_(F_a))
    + ||M_(F_a)|| * osc_e(W),

a*G_right a <= (1/2) * sum_e b_e(F_a)^2.
```

This is neither a global `|E_H|` worst-case replacement **nor an H-uniform conclusion**: `||W||`, `||M_F||` and their linkwise oscillations may all depend on volume. It makes the **exact remaining estimates** explicit.

## 3. ACTIVE P4-Q2 next steps — execute in order

### Q2-A. Ground the physical half-density `W` in original SU(2) one-link Wilson locality

**Already proved and available:**

- Right-link replacement changes the complete one-slab Wilson action by a **single target crossing term plus the touching spatial plaquettes**. There is no contribution from untouched plaquettes.
- The one-link action oscillation is at most `8`; the raw one-slab Boltzmann kernel has one-link comparison factor `exp(8*beta)`, independent of spatial volume.
- The strictly positive **continuous physical-vacuum representative** obeys the corresponding pointwise one-link Harnack comparison with factor `exp(8*beta)`.

**To prove next:** use the *exact original* joint half-density and positivity to obtain an explicit, justified one-link comparison or oscillation estimate for

```text
W_(beta)(A,B) = ||T_beta||^(-1) Omega_beta(B)
                / sqrt(rho_joint(beta;A,B)).
```

Keep normalization, the positive continuous joint density, the original pair-Haar/joint a.e. representatives and all endpoint positions explicit. A kernel comparison **alone** is not a bound on `W`: the vacuum and square-root density must be handled jointly. Seek a coefficient vanishing as `beta -> 0` when logically justified, and identify residual volume-dependent prefactors honestly. Do not infer finite spatial support of `W`.

**Candidate source chain** (all under `MGAP4D/MathlibAnalytic/`):

1. `PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalActionVariation.lean`
2. `PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds.lean`
3. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack.lean`
4. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack.lean`
5. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasure.lean`
6. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentVacuumReceiverDirichletLeibniz.lean`

**Acceptance:** Lean theorem about the actual `normalizedPhysicalOneSlabJointHalfDensityWeightBCF` update difference (or ratio), retaining the original `W` and a correct finite-H/`beta` constant. No proxy weight.

### Q2-B. Estimate the normalized physical mean `M_(beta_n,F_a)` without losing signed input

The existing `normalizedPhysicalOneSlabVacuumMeanJointBCF` is the **actual** signed frozen normalized-transfer receiver. The physical input `F_a` is a linear combination of actual fine-right Krylov factors. No pointwise positivity of `F_a` is assumed.

**To prove:** compare its right-link updates via the raw Wilson kernel's true target-local action increment, the physical normalization and the continuous vacuum denominator. A positive-kernel comparison for `K` does **not** directly compare two signed kernel integrals. Use a justified absolute/source-integral or Hilbert estimate before bounding the difference, and keep the genuine transfer `S`, beta scales, and source/output signs.

**Acceptance:** explicit physical `osc_e(M_(F_a))` estimate in terms of rigorously defined link/source local quantities, with no arbitrary proxy posterior and no unsupported vacuum-sector projection.

Possible existing inputs:

- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenOrbitVacuumReceiverL2.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentVacuumReceiverDirichletLeibniz.lean`
- `PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalKernelFactorization.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRightExplicitTwoCouplingBeta.lean`

### Q2-C. Close the link sum or signed covariance row, not just each one-link bound

Combine Q2-A and Q2-B with **#5326**. The target is a theorem whose hypotheses are discharged for the *actual* physical family, such as a bounded sum

```text
sup_(finite H) sum_(e in E_H) b_e(F_a)^2
    <= C(beta,physical family) * sum_j a_j^2
```

with a constant demonstrably independent of spatial volume. An alternative is the signed Schur criterion from **#5321**:

```text
sup_(finite H) sup_i sum_j |sum_e inner(r_(e,i),r_(e,j))|
    <= C.
```

The constant may need an explicit depth/scale/`beta` dependence and appropriate physical-family restrictions. Do **not** call a result uniform until every global `|E_H|`, operator floor `m_H(beta)^(-1)`, global action budget `B_H`, and coefficient-count factor is actually controlled.

**Important:** one-link Wilson locality does not imply finite support after `j>0` physical transfer iterations. To reach H-uniformity, prove locality/tail estimates or cancellation, rather than assuming compact support.

### Q2-D. Physically meaningful ℓ² / operator-norm closure

If Q2-C yields genuine signed covariance row bounds or a stronger spectral estimate, use #5321's **real symmetric Schur** theorem to conclude

```text
a*G_right a <= C * sum_j (a_j)^2.
```

Compare the resulting C to the finite-H coefficient-ℓ¹ estimate (#5319) and the direct linkwise-residual estimate (#5320). A mere Cauchy–Schwarz restatement introducing `r+1` or `|E_H|` is **not** the desired physical operator-norm improvement.

**Q2-C/D remain OPEN.** PR #5326 constructed the needed *objects*, not their volume-uniform summability.

## 4. Next after P4-Q2: independently required adjacent-scale work

| Gate | Required theorem | Current status |
| --- | --- | --- |
| **C1: physicality / leakage** | Control reconstructed candidates in the actual coarse **physical** space/common marginal; do not infer from posterior averaging. | OPEN |
| **C2: vector-wise transfer/reconstruction** | For each relevant finite `r,k`, control the actual difference between fine physical evolution/reconstruction and coarse physical transfer with a summable bound. | OPEN |
| **C3: explicit weighted beta trajectory** | Exhibit a trajectory for which actual original normalized-transfer response coefficients times `|beta_(n+1)-beta_n)|` are summable. | OPEN |
| **Fixed natural-time compatibility** | Derive consistent iterates of **one** limiting discrete-time physical operator, not merely unrelated limits at each m. | OPEN |
| **H2 physical time** | Establish the spacing-scaled generator/semigroup regime. Fixed `q0<1` at `a_n->0` alone gives `q0^(floor(t/a_n))->0` for `t>0`, not a nontrivial strongly continuous semigroup. | OPEN |
| **H3 OS Hamiltonian** | Construct and identify physical reconstructed generator, positivity, vacuum and self-adjointness. | OPEN |
| **H4 continuum mass gap** | Prove the required continuum Wightman/Yang–Mills spectral statement with a strictly positive mass gap. | OPEN |

Finite-volume transfer constants (`kappa_12 >= 1/2304`, `gap >= 1/3072`, `q0 = 3071/3072` in their proved contexts) do **not** bypass these stages.

## 5. Historical P3: keep as supporting formal results, not the active reconstruction loop

The P3 posterior seed/locality machinery is retained but **deferred** behind the genuine physical P4 route. Do not repeatedly rebuild its unsuccessful Dobrushin variants.

| P3 lane | Status | Source-level content |
| --- | --- | --- |
| Structural posterior-to-energy, #5208–#5225 | CLOSED | Original joint posterior `CondExpL2`, signed source link residual, true resampling, exact `1/6` six-color and `1/12` resampling normalizations, noncommuting projection path-loss union bound. |
| **P3-A**, #5227 | CLOSED | Four primary plaquette seed links, intrinsic seed distance, near/far split, `distance>2` remoteness criteria. |
| **P3-B1/B2**, #5228–#5230 | CLOSED | Full-local-factor posterior seed covariance decay, cubic shell majorant, uniform **full-local-factor** exterior covariance mass under its hypotheses. |
| **P3-B3**, #5234–#5235 | CLOSED pointwise | Exact `fullLocalFactor=boundaryTilt*sourceRightLinkTilt`; `exp(-6 beta)<=boundaryTilt<=exp(6 beta)`; literal source-only tilt covariance decay. |
| **P3-B4**, bridge from posterior covariance to the actual centered signed source-coordinate response | OPEN | Do **not** identify posterior covariance directly with its pair-Haar `L²` norm without a theorem. |
| **P3-C**, signed output drift / deweighted contrast #5231–#5233 | PARTIALLY CLOSED | Cross-input contrast cancels common drift, but single-input original loss retains its output/half-density term. |
| **P3-D**, full frozen initial link sum | OPEN | Any final P3 return must preserve actual source signs, shell sum, near links and distinct fine/frozen couplings. |

This historical material should not be labeled the latest mathematical frontier. The current live frontier is the genuine #5326 `W × M` linkwise physical control.

## 6. Closed no-go routes and forbidden shortcuts

**Proved limitations:**

- **Old H1-D5:** positive-SU(2)-coupling whole-operator compatibility is refuted; do not revive as exact top-vacuum alignment or a renamed global identity.
- **#5207 fixed-`s>8` strict-Dobrushin scaling:** the specific finite-positive-mass spacing-scaled certificate is incompatible with its stated conditions; **not** a no-go for all continuum approaches.
- **#5217 uncorrected sup-width majorants:** old uncorrected pointwise width estimates cannot deliver the desired route; the genuine signed-`L²` approach is different.

**Proof-integrity constraints:**

- Do not apply the fixed `q0` contraction to `|x|` without proving the absolute-value vector stays in the requisite sector.
- Never identify the original posterior `P_e`, pair-Haar conjugate `Q_e`, source-coordinate projection, or physical transfer/reconstruction.
- Preserve fourfold-a.e. and original retained-sigma conditions; do not swap a.e. with pointwise equality.
- Do not infer H-uniformity from **fixed-H** strict positivity, local Harnack bounds or a sum of locally bounded errors.
- Do not assume positive-depth Krylov inputs have strict finite spatial support; do not assume the nonlocal vacuum is finite-range merely because the raw plaquette action is local.
- Do not erase the true output drift from an individual defect on the strength of a distinct two-input cancellation.
- Do not replace noncommuting stagewise path loss by squared total displacement or concatenate the six same-initial-vector colors into one sweep.
- Keep the exact `beta_n` frozen versus `beta_(n+1)` fine scales, the `1/6` and `1/12` energy normalizations, and the genuine Wilson joint/posterior laws.
- No `sorry`, `admit` or new axioms in theorem-bearing additions.

## 7. Active source handoff (fresh exact HEAD only)

Paths have prefix `MGAP4D/MathlibAnalytic/`. Read in this order:

| Proof step | Exact source |
| --- | --- |
| F1/F2/F3 closure | `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalJointFourfoldAELifting.lean` → `...PairHaarRightLinkFiberDescent.lean` → `...PairHaarRightLinkRetainedAEDescent.lean` → `...PairHaarPositiveBetaVacuumFiberEnergy.lean` |
| Q1 fixed-H retained witnesses | `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalUnregularizedRetainedL2.lean` (#5309) |
| Q2 genuine unit and two-beta control | `...PairHaarUnitReceiverDirichletExplicitBeta.lean` (#5318), `...PairHaarUncenteredCoefficientL1Rayleigh.lean` (#5319) |
| Q2 exact link residual | `...PairHaarUncenteredLocalLinkwiseRayleigh.lean` (#5320) |
| Q2 signed Schur covariance | `...PairHaarUncenteredPosteriorCovarianceSchur.lean` (#5321) |
| Q2 original joint and fiber identities | `...PairHaarUncenteredOriginalJointConditionalCovariance.lean` (#5322), `...PairHaarUncenteredOriginalFiberCrossCovariance.lean` (#5323) |
| Q2 exact original two-copy energy | `...PairHaarUncenteredResamplingPolarization.lean` (#5324) |
| Q2 genuine per-link oscillation | `...PairHaarPhysicalPosteriorOscillation.lean` (#5325) |
| **Immediate theorem carrier** | **`PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityMeanLinkBudget.lean`** (#5326) |
| Local Wilson / vacuum inputs | `PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalActionVariation.lean`, `...OneSlabRightTargetLocalFactorBounds.lean`, `...PhysicalTransferContinuousVacuumPointwiseHarnack.lean` |
| Original physical product splitting | `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentVacuumReceiverDirichletLeibniz.lean` |

Ellipses in the table abbreviate the shared filename prefix `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacent` or `PeriodicHypercubicEvenSpecialUnitary`, **not** independent proof artifacts. Fetch the exact full path in GitHub at the authoritative SHA; never guess an import or use default `main`.

## 8. PR completion protocol and next deliverable

1. Freshly reobserve the authoritative branch exact SHA; examine the actual Lean definitions, existing proof dependency APIs and the current physical coefficient definitions.
2. Implement **one substantive Q2-A theorem**: an actual original-Wilson half-density factor `W` right-link ratio/oscillation consequence of proved local action + physical vacuum Harnack (or a rigorously diagnosed obstruction). No new surrogate law or assumed volume-independent global norm.
3. Inspect **the entire new Lean file and all affected dependencies**, not only CI error line numbers. Fix pinned Lean/mathlib elaboration issues, including equality orientation, norm conversions, measurability and local instances.
4. Require an exact PR head with **Lean job SUCCESS**, **matching MCP completion receipt SUCCESS**, **zero changed-file warnings/errors** and **no new sorry/admit/axiom**. Only then merge.
5. Reobserve the theorem carrier HEAD and update the proof-status table separately if the math actually advances.

For this docs revision, the last independently verified theorem evidence is [PR #5326](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5326), source SHA `6677af987415248a619039b32138a663aaf31210`, [exact-head CI run 37910157743](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37910157743), changed Lean job `113753105635`, matching receipt `113754562387`, build **10,426 / 10,426**, new-file diagnostics **0 / 0**, merge SHA `ae59199bb6b4a1a6d3afb31f3e9b5fb2a411727c`. This **documentation-only** PR is not a new theorem; its diff should contain **only `README.md` and `ROADMAP.md`**.

**Immediate next milestone:** a fully original, physical SU(2) frozen-`beta` one-link estimate for the #5326 half-density `W`, followed by signed physical mean `M_(F_a)` link variation, leading to a truly summable/H-independent Gram coefficient **if the mathematics supports it**. Keep continuum claims out until H2–H4 are actually completed.
