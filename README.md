# MGAP4D — four-dimensional Yang–Mills formalization

Hidetoshi Itakura's Lean 4 / mathlib development toward the four-dimensional Yang–Mills existence and mass-gap problem.

**Theorem-bearing checkpoint (2026-10-09 JST): [PR #5326](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5326), merged as `ae59199bb6b4a1a6d3afb31f3e9b5fb2a411727c`.** This SHA is the last theorem-bearing merge verified for this documentation revision. A later documentation-only merge will move the authoritative branch HEAD without adding a theorem.

> **Scope:** A substantial body of *finite-volume* original Wilson SU(2) results is machine-checked, including strict positive-`beta` posterior vacuum energy at each fixed finite volume and exact physical Krylov Gram/resampling identities. **No volume-uniform positive-`beta` bound, continuum Yang–Mills theory or positive continuum mass gap is claimed.**

See [ROADMAP.md](ROADMAP.md) for precise completed gates, unresolved estimates, and the next proof order.

## 1. Repository authority and verified environment

| Field | Authoritative value |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| **Only theorem-bearing branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Verified theorem-bearing merge | **#5326 — `ae59199bb6b4a1a6d3afb31f3e9b5fb2a411727c`** |
| #5326 exact PR head | `6677af987415248a619039b32138a663aaf31210` |
| Lean pin (`lean-toolchain`) | `leanprover/lean4:v4.30.0-rc2` |
| mathlib pin (`lake-manifest.json`) | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact-head PR CI | [run 37910157743](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37910157743) — **SUCCESS** |
| Changed Lean job / matching MCP receipt | `113753105635` / `113754562387` — **SUCCESS / SUCCESS** |
| Changed Lean build / diagnostics | **10,426 / 10,426** jobs; changed file **0 warnings / 0 errors**; no new `sorry` / `admit` / `axiom` |

GitHub's default `main` **is not theorem authority**. For new work, observe the **fresh exact HEAD of the theorem-bearing branch**, inspect formal Lean artifacts at that SHA, then consult this README/ROADMAP, exact-head CI and finally historical conversation notes. Docs-only merges change branch SHA **without** changing the last theorem-bearing baseline.

## 2. What is actually proved

### 2.1 Structural finite-volume foundations

- The original normalized physical one-slab SU(N)/SU(2) Wilson transfer, real Hilbert space and pair-Haar carrier, with ground-state half-density isometry `U_beta`. The true joint single-right-link conditional expectation `P_(beta,e)` transports to the pair-Haar projection `Q_(beta,e) = U_beta^(-1) P_(beta,e) U_beta`.
- Real original-joint conditional expectations, chronological (not generally commuting) one-link schedules and exact projection-loss/resampling-energy identities (#5208–#5225, #5263–#5273).
- Finite-volume coercive transfer bounds in their stated regimes: `kappa_12 >= 1/2304`, gap `>= 1/3072`, and `q0 = 3071/3072`. These are **not** a physical continuum mass-gap theorem.
- Actual frozen `beta = 0` pair-Haar receiver rank-one/collapse and vanishing original posterior residual Gram, **with the separate fine-`beta` condition treated correctly** (#5274–#5279).

The original six-color initial energy uses the exact `1/6` residual normalization and `1/12` two-copy resampling normalization. These constants must not be changed by subsequent estimates.

### 2.2 P4-F1/F2/F3: CLOSED — finite-volume positive-beta Wilson vacuum

| Gate | Closed Lean result | Sources |
| --- | --- | --- |
| **F1** | Lift the pair-Haar-a.e. original/continuous Wilson density identity to **all four crossed entries simultaneously**; the original joint-density strict-minor set has positive fourfold Haar measure. | #5296–#5299 |
| **F2** | Establish single-right-link fiber nonconstancy and descend it through the **original retained-right-link sigma algebra**, preserving all left/off-target context and a.e. distinctions. | #5300–#5301 |
| **F3** | The **genuine original positive-`beta` posterior vacuum-fiber energy is strictly positive** for each finite spatial volume and `beta > 0`. | **#5302** |

In particular, for the original transported vacuum `U_beta(1)`, define

```text
E_vac(beta,H) :=
  sum_e ||(I - P_(beta,e)) U_beta(1)||^2.
```

PR #5302 proves `E_vac(beta,H) > 0` for each fixed finite `H` and positive `beta`. The proof goes through original-law a.e. nonretained measurability, **not** an illicit pointwise substitution of an arbitrary `L²` representative. This strictness is **not** uniform in `H` or `beta`.

### 2.3 P4-Q1: genuine finite-volume quantitative Wilson vacuum energy — CLOSED at finite H

PRs #5303–#5309 construct retained-right-link approximants inside the **original joint `L²` law**, and prove an explicit local Wilson Harnack square-root-ratio estimate. The final unregularized witness is retained-measurable and gives

```text
0 < E_vac(beta,H)
    <= |SpatialLinks(H)| * (exp(16*beta) - 1)^2    (beta > 0).
```

The per-link factor `(exp(16*beta) - 1)^2` is volume-independent; the **all-link bound still contains the number of spatial links**. Neither this inequality nor its strict lower bound provides the volume-uniform energy required for a continuum argument.

Key artifact: `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalUnregularizedRetainedL2.lean` (#5309).

### 2.4 P4-Q2: genuine uncentered right-Krylov Gram — current frontier through #5326

Let `R_(n,j)` be the **actual uncentered** fine-right physical Krylov orbit, evolved using `beta_(n+1)`, and let `V_(beta_n)` be the **frozen** physical pair-Haar receiver using `beta_n`. For each original spatial link `e` write

```text
r_(e,j) := (I - Q_(beta_n,e)) V_(beta_n)(R_(n,j)).
G_right(i,j) = sum_e inner(r_(e,i), r_(e,j)).
F_a := sum_j a_j R_(n,j).
```

The finite Gram is positive semidefinite, and its Rayleigh form has the following **exact original-Wilson** resampling identity (#5324):

```text
a* G_right a
  = sum_e ||(I - Q_(beta_n,e)) V_(beta_n)(F_a)||^2
  = (1/2) * sum_e E_resample(beta_n,e; F_a).
```

Here `E_resample` integrates the **squared two-copy right-link update of the full signed physical joint observable** against the genuine original joint Wilson law and its original posterior conditional law; it is not a surrogate probability measure.

Proven quantitative and structural steps:

| PR(s) | Actual achievement |
| --- | --- |
| #5310–#5313 | Genuine constant-orthogonal positive-`beta` receiver estimates, explicit **finite-H** `O_H(beta)` amplitude / `O_H(beta²)` energy, and distinct frozen/fine coupling control. |
| #5314–#5315 | Centered and **uncentered** Krylov Gram identities, vacuum/excitation decomposition, weighted two-coupling Rayleigh structure. |
| #5316–#5318 | Anchor the genuine unit receiver to original vacuum and physical receiver drift, with explicit finite-H budget `E_unit <= 2|E_H|(D_H(beta)^2 + (exp(16 beta)-1)^2)`. |
| #5319 | Fully explicit **coefficient-ℓ¹** two-coupling Rayleigh estimate; volume factors remain visible. |
| #5320 | Link-resolved original posterior residuals `d_(e,j) = ||r_(e,j)||` and exact `sum_e (sum_j |a_j| d_(e,j))²` upper envelope. |
| #5321 | **Signed** link/mode covariance `K_ij = sum_e inner(r_(e,i),r_(e,j))` and an **ℓ² Schur Rayleigh theorem conditional on a proved covariance row bound**. |
| #5322–#5323 | Exact representation via original-joint `CondExpL2` covariance loss and signed **literal original posterior-fiber cross integrals**. |
| #5324 | Exact original two-copy resampling polarization: `8 inner(r_(e,i),r_(e,j)) = E_e(R_i+R_j) - E_e(R_i-R_j)`; the exact total Rayleigh identity above. |
| #5325 | True original-Wilson one-link oscillation control: `E_e(F) <= integral b_e(z)^2 dmu_joint` for **certified** physical BCF update differences, with zero loss for an update-invariant observable. |
| **#5326** | **Constructed**, not assumed, linkwise bound from the real half-density and physical mean factors of the genuine joint receiver. |

For the last statement, use the **existing exact factorization** `V_joint(F_a)=W_(beta_n) M_(beta_n,F_a)`. Define `osc_e(X)` as the norm of the original joint bounded-continuous-function difference `X(z)-X(z[e <- g])`, with the new group value `g` included in the compact carrier. PR #5326 proves

```text
b_e(F_a) :=
  ||W|| * osc_e(M_(F_a)) + ||M_(F_a)|| * osc_e(W),

|V_joint(F_a)(z) - V_joint(F_a)(z[e <- g])| <= b_e(F_a),

a* G_right a <= (1/2) * sum_e b_e(F_a)^2.
```

These are **fully constructed physical finite-volume quantities**. The BCF sup norms, both factor oscillations, the link sum and the coupling dependence can still depend on `H`. **No volume-uniform bound, spatial decay or ℓ² operator-norm estimate with an H-independent constant has been proved.**

## 3. What remains open (critical distinction)

1. **Actual linkwise locality/summability.** Bound `osc_e(W)` and `osc_e(M_(F_a))` using the exact Wilson plaquette action, the continuous ground-state/Doob response, and the genuine signed physical input. Establish a link-sum estimate **uniform in finite volume** or a rigorous obstruction. The physical vacuum dependence cannot be declared finite-range merely because the raw Wilson action is local.
2. **Physical covariance/Schur completion.** Prove the signed mode-pair covariance row estimate required by #5321 with a uniform constant, or an alternative independently justified operator-norm bound. Do **not** merely relabel a coefficient-ℓ¹ or cardinality estimate as ℓ² progress.
3. **Adjacent-scale reconstruction.** Common-marginal physicality/leakage (C1); actual vector-wise reconstruction/transfer compatibility (C2); appropriately weighted explicit `beta` trajectory (C3). Preserve `beta_n` versus `beta_(n+1)`.
4. **Physical continuum time and mass gap.** Spacing-scaled generator / nontrivial strongly continuous semigroup (H2), OS Hamiltonian reconstruction (H3), and Wightman energy–momentum spectrum with a positive continuum mass gap (H4).

Independent finite-volume results, original posterior strict positivity and local Harnack bounds **do not close these obligations automatically**.

## 4. Existing Wilson locality tools (do not overinterpret)

Earlier Lean artifacts prove the **actual one-link right-boundary Wilson action** changes only through the target crossing term plus the intrinsic spatial plaquettes touching that link. They also establish a volume-independent one-link action oscillation bound `8`, corresponding raw Wilson kernel comparisons with factor `exp(8*beta)`, and positive continuous physical-vacuum one-link Harnack comparisons.

These are genuine local inputs, **not** yet a bound on the total true uncentered receiver's link-summed energy. Its `W` half-density/output term and `M` normalized physical-transfer receiver must both be controlled. The proof target after #5326 is the actual physical linkwise coefficient and its spatial sum, not another generic Dobrushin contraction.

Relevant code includes:

- `PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalActionVariation.lean`
- `PeriodicHypercubicEvenSpecialUnitaryOneSlabRightTargetLocalFactorBounds.lean`
- `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumLocalHarnack.lean`
- `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPointwiseHarnack.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentVacuumReceiverDirichletLeibniz.lean`

All paths above live under `MGAP4D/MathlibAnalytic/`.

## 5. Where to resume the proof

Inspect this **minimal active theorem chain**, always from the newly observed authoritative branch SHA (prefix filenames with `MGAP4D/MathlibAnalytic/`):

1. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarCanonicalUnregularizedRetainedL2.lean` — original Q1 quantitative vacuum bound (#5309).
2. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverDirichletExplicitBeta.lean` — finite-volume unit receiver (#5318).
3. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredCoefficientL1Rayleigh.lean` — explicit two-`beta` estimate (#5319).
4. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredLocalLinkwiseRayleigh.lean` — physical link residuals (#5320).
5. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredPosteriorCovarianceSchur.lean` — signed Schur row criterion (#5321).
6. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredOriginalJointConditionalCovariance.lean` — original conditional covariance (#5322).
7. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredOriginalFiberCrossCovariance.lean` — original posterior fiber integrals (#5323).
8. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredResamplingPolarization.lean` — exact two-copy resampling identities (#5324).
9. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalPosteriorOscillation.lean` — true one-link observable oscillations (#5325).
10. **`PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityMeanLinkBudget.lean`** — constructed `W/M` linkwise bound, latest theorem (#5326).

For the completed F1/F2/F3 descent, see `...PairHaarOriginalJointFourfoldAELifting.lean`, `...PairHaarRightLinkFiberDescent.lean`, `...PairHaarRightLinkRetainedAEDescent.lean` and `...PairHaarPositiveBetaVacuumFiberEnergy.lean` (full filenames share the `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacent` prefix).

The historical P3 (#5227–#5235) seed-distance / source-only tilt / covariance route remains **supporting formal infrastructure, not the active blocking path**. Avoid rebuilding failed Dobrushin architectures; see the archived obligations in [ROADMAP](ROADMAP.md).

## 6. Reproduction and audit discipline

After checking out the authoritative branch at a **fresh exact SHA**, preserve `lean-toolchain` and `lake-manifest.json`. The named latest theorem target can be built with:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityMeanLinkBudget
```

For any **theorem-bearing** PR: review every changed Lean file *and its dependencies*, inspect the actual Lean failure reasons rather than only the CI-highlighted lines, prohibit new `sorry`/`admit`/`axiom`, require successful exact-head Lean CI and matching MCP completion receipt, then merge. Prior successful source heads must not be confused with a newly observed authoritative branch HEAD.

For a **documentation-only** PR: require only `README.md` and `ROADMAP.md` in the diff, keep all Lean/toolchain/manifest sources unchanged, and identify the docs-only merge as a documentation update rather than a new theorem.

## 7. Guardrails / prior no-go results

- The old whole-operator **H1-D5** compatibility route is refuted at positive SU(2) coupling; do not recreate it under another label.
- The #5207 fixed-`s>8` strict-Dobrushin finite-positive-mass scaling certificate fails in its specified regime. This is **not** a no-go for all continuum approaches.
- The #5217 old uncorrected sup-width majorants remain inadequate; newer signed/original-posterior estimates do not negate that result.
- Do not feed `|x|` into the `q0` excited-sector contraction without proving sector preservation, confuse the distinct projections, equate a.e. identities with pointwise ones, assume positive transfer depth has compact spatial support, or replace noncommuting path loss by squared total displacement.
- Strict finite-H posterior positivity, finite-H `O_H(beta²)` bounds, and the constructed #5326 sum **do not prove** a volume-uniform gap or a continuum mass gap.

**Research status:** P4-F1/F2/F3 and finite-H P4-Q1 quantitative results are **closed**; P4-Q2 has an actual signed, original-law, physically constructed linkwise Gram interface through #5326; **uniform spatial control and continuum reconstruction remain open**.
