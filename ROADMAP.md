# MGAP4D Roadmap

**Status date: 2026-10-08 JST — authoritative theorem-bearing snapshot: merged PR #5297, SHA `076244eb8b9899c513a9b6fff3e50b6bb1277b37`.**

This roadmap keeps proven finite-volume physical Wilson identities, conditional interfaces, no-go routes and open continuum obligations separate. **No theorem here claims a completed four-dimensional continuum Yang--Mills mass gap.** The active proof strategy is the *non-Dobrushin P4 physical posterior/Wilson crossing route*; the P3 source-tilt locality program below is historical supporting work.

## 0. Authority checkpoint

| Item | Verified theorem-bearing checkpoint |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| Unique authoritative branch | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing PR | **#5297, merged** |
| Latest theorem merge SHA | `076244eb8b9899c513a9b6fff3e50b6bb1277b37` |
| Validated PR head | `e133452d5f29ea9eab74a23be32b2435b8d1ac5d` |
| Pinned Lean / mathlib | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

Authority order is fixed: (1) **fresh exact authoritative branch HEAD**, (2) Lean definitions/theorems at that SHA, (3) README/ROADMAP, (4) exact-head CI receipt, (5) conversation history. The GitHub default `main` is **not** the theorem carrier. A docs-only merge changes the branch HEAD but not the latest theorem-bearing SHA.

## 0A. ACTIVE P4 — proven finite-volume route

| PR range | Actual Lean status |
| --- | --- |
| #5267--#5273 | Genuine right Krylov/left-three-mode residual Gram and Rayleigh identities; quantitative volume-uniform diagonal control remains conditional |
| #5274--#5279 | Beta=0 physical rank-one and **zero true posterior residual/Gram**; fine-beta-zero assumptions are kept distinct |
| #5280--#5282 | Exact beta-zero-anchored two-drift decomposition; original posterior projection drift factors through one constant physical vacuum |
| #5284--#5286 | Sharp retained-context `L²` witness Pythagoras; inverse-sqrt Wilson vacuum under true joint law; exact zero-energy iff retained measurability (nonmeasurability itself is not yet proved) |
| #5287, #5289--#5290 | Rank-one positive-beta projection-drift Gram, exact Rayleigh and *conditional* no-mode-count physical upper bound |
| #5292 | Exact constant/orthogonal receiver decomposition; for constant-orthogonal combined input, **physical Gram Rayleigh = receiver drift**, not merely an upper bound with factor two |
| #5293--#5294 | Exact physical normalized Wilson joint minor factorization; symmetric SU(2) kernel minor governed by `1-crossing(A,B)^2` and positive half-weights |
| #5295 | Explicit single-link `SU(2)` rotation `R(pi)` gives `crossing_beta(A,B)=exp(-2 beta)<1` and an actual strictly positive one-slab kernel minor for every finite H and beta>0 |
| #5296 | **Canonical continuous positive physical vacuum** produces `W_{beta,c}` equal to the original normalized Wilson joint density **pair-Haar a.e.**; explicit strictly positive pointwise joint minor |
| **#5297 — latest** | Strict-minor locus of continuous `W_{beta,c}` is a **nonempty open set of strictly positive fourfold spatial Haar measure**, for each beta>0 and each finite H |

### What #5297 closes — and what it does not

**CLOSED:** the positive-beta physical crossing witness is not merely an exceptional isolated point of the continuous joint representative. Its signed 2×2 minor remains positive on a positive-measure four-boundary event. This is an actual finite-volume mathlib theorem.

**NOT CLOSED:** (1) transfer of fourfold equality to original L²-based density via explicit a.e. lifting/Fubini; (2) reduction from positive fourfold crossing minors to **nonmeasurability with respect to at least one original retained-right-link sigma algebra**; (3) a positive-volume-independent bound for the genuine all-link vacuum energy or the true receiver drift; (4) spacing-scaled physical generator and continuum mass gap. Finite-volume positivity is not a uniform gap estimate.

### 0A.1 ACTIVE next-step priorities

| Priority | Goal and exact proof obligation | Status |
| --- | --- | --- |
| **P4-F1** | Lift `W_{beta,c}=W_beta` (pair-Haar a.e.) to the four entries of each original fourfold minor, respecting independent boundary configurations and null sets | OPEN |
| **P4-F2** | Connect the positive fourfold Wilson minor event to an original **right-link retained-σ nonmeasurability** theorem; prove any needed single-right-link descent, conditional section, and Fubini statements, without assuming pointwise equality of `L²` representatives | OPEN |
| **P4-F3** | Feed a real nonretained-right-link witness into #5286 to deduce **strict positive-beta genuine posterior-fiber vacuum energy** for fixed finite H (only after F2) | OPEN |
| **P4-Q1** | Build retained-measurable local witnesses `g_e` under the original joint posterior and prove a **summable, volume-uniform** `L²` error (or an obstruction), using #5284 and true Wilson variation | OPEN |
| **P4-Q2** | Independently establish original positive-beta physical **receiver drift** `A_beta(f)` bounds independent of volume (or expose their obstruction); combine with #5289--#5290 only when hypotheses are discharged | OPEN |
| **Continuum** | Establish spacing-scaled generator estimates, compatible physical-time limits, OS/Wightman reconstruction, and the desired continuum mass gap | OPEN |

For the current algebraic state, let `F = sum_i a_i f_i`. PRs #5287 and #5289 prove `a^T B_beta a = inner(unit,F)^2 E_beta^vac`; #5290 proves `a^T G_beta a <= 2(Cdrift+Cvac)||F||²` **only if** `A_beta(g) <= Cdrift ||g||²` for all physical `g` and `E_beta^vac <= Cvac`. On the combined constant-orthogonal sector #5292 gives the stronger exact identity `a^T G_beta a = A_beta(F)`.

**Do not restart Dobrushin by default.** Keep actual frozen beta in `Q_{beta,e}` distinct from the fine beta in the right Krylov orbit; use the original Wilson measure and half-density throughout.

## 0B. Historical P3 record

Sections 1--3 below preserve proved posterior/seed/source-tilt structures through #5235 and the older P3 objectives, but they are historical/supporting material, not the current immediate proof route.

## 1. Closed structural chain — do not reconstruct

| Range | Established result |
| --- | --- |
| #5208--#5212 | Literal posterior fiber law -> genuine joint CondExpL2 -> arbitrary chronological schedules -> exact stage-residual energy |
| #5214--#5218 | Actual prefix variation propagation, fixed-color enumeration, six-color profile, L2 stability, continuous scalar majorants, left-centered comparison |
| #5219 | fineFrozenBCF exactly represents the unchanged frozen vector; approximation error zero |
| #5220 | One-link L2 envelope including half-density variation |
| #5221 | Noncommuting projection union bound; path-loss energy <= 4 I(f) |
| #5222 | Signed link-local residual energy and exact set/complement splitting |
| #5223 | Exact posterior resampling identity B_e = (1/2) Q_e and I = (1/12) sum Q_e |
| #5224 | Exact source-only Wilson tilt factorization of a right-link update, with output drift retained |
| #5225 | One-source-coordinate pair-Haar CondExpL2 projection and exact centered signed-response decomposition |

The actual frozen convention remains fixed:

x_(n,r,k) = T_hat_(n+1,beta_(n+1))^r phi_(n+1,k),

while the final frozen transfer and joint half-density use beta_n. Keep r = 0.

## 2. Historical P3 — quantitative locality of the actual initial residual sum (deferred)

Main object:

I_n(f_frozen(n,r,k))
  = (1/6) sum_e ||(I - P_(n,e)) f_frozen||_2^2
  = (1/12) sum_e Q_(n,e)(x_(n,r,k)).

The objective is a volume-uniform or summable spatial bound on this exact quantity, strong enough for the existing adjacent-scale receivers.

### P3-A. Geometric seed-distance interface — CLOSED

PR #5227 defines the four canonical primary-plaquette seed links, intrinsic seed distance, and near/far finite link sets.

It proves:

- seed distance is zero on the seed;
- near and far sets partition the finite spatial links;
- seed distance > 2 implies the distinctness and plaquette-remoteness hypotheses needed by the existing #5199 posterior covariance theorem;
- r = 0 remains the actual primary-plaquette Gram-Schmidt seed before the frozen coarse-coupling transfer.

No hard support claim is made for positive transfer depth.

### P3-B1. Full-local-factor seed covariance — CLOSED

PR #5228 transfers #5199 to the primary seed:

|Cov(seedLocalFactor, remoteFullLocalFactor)|
  <= covariancePrefactor(s,beta) / s^(seedDistance),

under the original cutoff and remoteness hypotheses.

This is genuine seed-distance decay when s > 1.

### P3-B2. Volume-independent shell geometry — CLOSED

PR #5229 proves a uniform cubic shell majorant for the number of links at exact seed distance r.

PR #5230 combines that shell majorant with the full-local-factor covariance decay and obtains a volume-independent completed covariance mass on the radius-two exterior.

Therefore the geometry/summability mechanism itself is closed for the full local factor.

### P3-B3. Literal source-only tilt covariance — CLOSED POINTWISE

PR #5234 proves the exact factorization

fullLocalFactor = boundaryTilt * sourceRightLinkTilt,

where boundaryTilt is independent of the posterior integration variable. It also proves exact covariance scaling through that scalar.

PR #5235 proves:

- absolute half-action boundary increment <= 6;
- exp(-6 beta) <= boundaryTilt <= exp(6 beta);
- boundaryTilt^(-1) <= exp(6 beta);
- seed-distance covariance decay for the literal sourceRightLinkTilt used in the signed joint response:

|Cov(seedLocalFactor, sourceRightLinkTilt)|
  <= exp(6 beta) * covariancePrefactor(s,beta)
     / s^(seedDistance).

Both distance > 2 and radius-two-exterior forms are available.

**Status:** pointwise source-only covariance decay is closed. A summed source-only covariance-mass theorem analogous to #5230 has not yet been recorded and is a natural next composition.

### P3-B4. Centered source-coordinate bridge — OPEN / CENTRAL

The missing theorem is now sharply isolated.

The actual signed source response uses

C_e^src(x,z)
  = source-coordinate CondExpL2 of
    [J(.,z) x - O_x(z)].

The proved posterior covariance theorems live on a one-slice posterior law. No theorem yet identifies

||C_e^src||_2,

its integrated square, or the actual frozen signed response with the seed/source-only posterior covariance from #5235.

Acceptable next routes include:

1. an exact posterior-to-pair lift showing a concrete frozen or finite-mode signed response is a posterior covariance with sourceRightLinkTilt;
2. a direct duality theorem controlling the source-coordinate projection by a family of local posterior covariances;
3. a direct distance-sensitive bound on the integrated centered source-coordinate contribution, without passing through a norm identity.

Do not assert a covariance-to-source-coordinate-norm identity without proving it.

### P3-C. Output/half-density drift — PARTIALLY CLOSED

PR #5231 gives the exact pointwise square split of the original defect into:

- retained output/half-density drift;
- centered source-coordinate envelope.

Thus the original single-input defect still contains a genuine scalar drift term.

PR #5232 proves that for two signed inputs the cross-multiplied contrast cancels both the common scalar output drift and the common source-tilt mean exactly:

O_v D_x - O_x D_v
  = Out * (O_x <C_v,Tilt> - O_v <C_x,Tilt>).

PR #5233 removes the strictly positive Out factor exactly:

Out^(-1) (O_v D_x - O_x D_v)
  = O_x <C_v,Tilt> - O_v <C_x,Tilt>.

No observable is divided by.

**Status:** drift cancellation is closed for the proved cross contrast, but the original Q_e energy is not yet replaced by that contrast. If the final P3 receiver continues through the original one-input Dirichlet form, the scalar drift still needs an integrated bound. If a theorem-generated contrast representation replaces it, that replacement must be proved explicitly.

### P3-D. Return to the full Dirichlet sum — OPEN

Required final P3 closure:

- combine the centered-source or contrast estimate with the exact 1/12 Dirichlet normalization;
- sum the exterior using the proved seed shell geometry;
- control the finite near-link part;
- preserve the actual frozen family and both beta scales;
- produce a volume-uniform or explicitly summable bound on the whole I_n.

A target of the form

4 I_n <= C_(r,k) * rho^D / (1 - rho),   0 <= rho < 1,

is still a goal, not a theorem.

## 3. Historical P3 deliverables (deferred behind current P4)

Priority order:

### D1. Sum the #5235 source-only covariance decay

Reuse the #5229/#5230 shell machinery and record a volume-independent radius-two-exterior mass bound with the explicit exp(6 beta) prefactor.

This is mainly a composition theorem and should not introduce new model assumptions.

### D2. Posterior covariance -> actual signed source response

Construct the exact bridge between a concrete seed/frozen observable and the deweighted centered source contrast or sourceLinkResponse.

Preferred properties:

- no division by O_x or O_v;
- no top/vacuum alignment hypothesis;
- no hard support claim after positive transfer depth;
- preserve signed cancellation;
- work on the existing pair-Haar and posterior carriers.

### D3. Return to Q_e

Convert D2 into an integrated square bound for the original resampling contribution, or prove a new exact receiver showing the relevant contrast controls the same energy.

Only after this step should P3 be regarded as closed.

## 4. Independent adjacent-scale obligations

### C1. Common-marginal physicality — OPEN

Control the actual leakage of reconstructed candidates from the coarse physical range.

Do not infer physicality from posterior averaging or source-coordinate localization.

### C2. Physical transfer / reconstruction commutation — OPEN

For each fixed finite r,k, control the actual vector-wise mismatch between fine transfer followed by reconstruction and coarse physical transfer.

A summable vector-wise bound is sufficient. Whole-space operator-norm convergence is not required and must not be substituted for the refuted H1-D5 route.

### C3. Weighted beta trajectory — OPEN INPUT

Prove summability for an explicit trajectory of the already-defined same-volume normalized physical-transfer beta-response coefficient multiplied by |beta_(n+1) - beta_n|.

Small unweighted increments alone are insufficient.

## 5. Fixed-natural-time closure and later physical layers

Once P3, C1, C2 and C3 are supplied, existing receivers can produce fixed-natural-time Cauchy/strong limits and the already-proved q0^m decay for the theorem-generated excitation under their hypotheses.

Still separate:

1. **One limiting discrete-time operator:** fixed-m limits do not automatically define compatible iterates of one operator.
2. **H2 physical time:** if a_n -> 0 while a fixed q0 < 1 controls the sector, then q0^(floor(t/a_n)) -> 0 for t > 0. A nontrivial strongly continuous semigroup needs spacing-sensitive operator or generator scaling.
3. **H3 OS Hamiltonian:** construct and identify the physical Hilbert space and generator with the required positivity, self-adjointness and vacuum properties.
4. **H4 Wightman / spectral mass gap:** verify continuum reconstruction and the intended Yang--Mills energy-momentum spectral statement.

## 6. Closed no-go routes

### N1. Old completed H1-D5

At positive SU(2) coupling, the old whole-operator compatibility forces rank-one behavior incompatible with the constructed finite sector. Do not restore it as exact vacuum/top alignment, exact completed cross-scale transfer compatibility, or an equivalent whole-space identity.

### N2. #5207 fixed-s strict-Dobrushin finite-positive-mass certificate

For fixed s > 8, the existing strict-Dobrushin scaling certificate cannot simultaneously realize a_n -> 0 and a finite positive spacing-scaled mass rate.

This does not rule out every continuum route.

### N3. #5217 old sup-width initial majorants

The limitation of the old uncorrected uniform sup-width majorants remains valid. The signed L2 route is a different route, not a repeal.

## 7. Forbidden shortcuts

- Do not apply q0 to |x|; non-top preservation after absolute value is unproved.
- Do not identify posterior projection, source-coordinate projection, physical transfer and coarse physical projection.
- Do not replace joint-a.e. identities by pointwise identities on exceptional fibers.
- Do not infer original right-link retained-sigma nonmeasurability from a pointwise or positive-fourfold-Haar crossing event without the required fourfold a.e./Fubini and right-link descent theorems.
- Do not infer a positive-beta volume-uniform gap from a strictly positive fixed-volume Wilson crossing minor or posterior energy.
- Do not infer locality from compactness, BCF density, finite-dimensionality or positivity.
- Do not infer hard support for the positive-depth frozen orbit.
- Do not concatenate the six colors into one sweep when the theorem treats six sweeps from the same initial vector.
- Do not replace noncommuting path loss by squared total displacement.
- Preserve the exact 1/6 six-color normalization and 1/12 resampling normalization.
- Do not delete the scalar output drift from an individual defect merely because the cross contrast cancels it.
- Do not identify posterior covariance with ||C_e^src||_2 without an explicit theorem.
- Preserve the distinction between beta_(n+1) in the orbit and beta_n in the final frozen transfer / joint law.

## 8. Source-level handoff

### Current P4 source order — read first

All paths below are relative to `MGAP4D/MathlibAnalytic/` and must be fetched at the **fresh exact authoritative HEAD**. Do not use GitHub's default `main` for these proofs.

1. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGramDiagonalRayleighCriterion.lean`
2. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFrozenZeroAllLinkVanishing.lean`
3. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredDrift.lean`
4. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredProjectionRankOne.lean`
5. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredVacuumJointVariance.lean`
6. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumRetainedWitnessPythagoras.lean`
7. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness.lean`
8. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumZeroIffRetainedWilson.lean`
9. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaProjectionDriftRankOneGram.lean`
10. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaDriftRayleigh.lean`
11. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaDriftRayleighHilbertCriterion.lean`
12. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaOrthogonalReceiverExact.lean`
13. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarWilsonJointCrossingMinor.lean`
14. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarWilsonJointDiagonalMinor.lean`
15. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarConcretePositiveBetaCrossingWitness.lean`
16. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointCrossingWitness.lean`
17. **`PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointCrossingPositiveMeasure.lean`** — latest positive-fourfold-Haar theorem

For future F1/F2 work also inspect the existing original ground-state measure, original `CondExpL2` projection, spatial Haar full-support/finite product instances, and `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumRepresentative.lean`.

### Historical P3 source-only-tilt/covariance handoff — do not mistake for the active frontier

1. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance.lean`
2. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay.lean`
3. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedPolynomialShell.lean`
4. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceMass.lean`
5. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateProjection.lean`
6. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateL2.lean`
7. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDefectSplit.lean`
8. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateContrast.lean`
9. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDeweightedContrast.lean`
10. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorSourceTiltCovarianceFactorization.lean`
11. `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSourceTiltSeedCovarianceDecay.lean`

Retain #5199 posterior covariance, #5221 noncommuting union bound, #5223 literal resampling Dirichlet, #5219 frozen BCF as historical supporting inputs.

## 9. Verification evidence

| Evidence | Latest theorem-bearing receipt |
| --- | --- |
| #5297 PR head | `e133452d5f29ea9eab74a23be32b2435b8d1ac5d` |
| PR Lean Fast Check | [run 37761412979](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37761412979) — SUCCESS |
| Changed Lean job | 113258448809 — SUCCESS |
| Matching MCP completion receipt job | 113259999219 — SUCCESS |
| Build and new-file diagnostics | **10,398 jobs built**, zero new warning/error, sorry/admit 0 |
| Theorem-bearing merge | `076244eb8b9899c513a9b6fff3e50b6bb1277b37` |
| Post-merge exact-SHA CI | [run 37761946518](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37761946518) — SUCCESS |

For theorem PRs: re-observe the authoritative SHA, check all changed Lean source plus dependencies/typeclass synthesis, ensure **actual changed-Lean job success** and a **matching exact-head MCP receipt**; no failing Lean job may be masked by a successful receipt publisher, and no new sorry/admit/axiom is acceptable.

For docs-only PRs: compare against fresh authoritative HEAD; require **README.md and ROADMAP.md only** and do not describe the resulting merge as a theorem advancement. Always separate the latest theorem-bearing merge SHA from subsequent docs-only branch HEAD.

## 10. Immediate next milestone

**P4-F1/F2 first: establish a real fourfold a.e. bridge and retained-right-link descent from the strictly positive crossing-minor event proved in #5297.**

For every finite H and beta>0, #5296--#5297 now provide an authentic continuous Wilson joint representative `W_{beta,c}` equal to the original density **pair-Haar almost everywhere**, and a nonempty open **fourfold Haar-positive** strict-minor event. These are definitive finite-volume statements, not merely a possible or hypothetical witness.

**Next mathematical deliverables:**

1. Prove that all four pair entries `W_beta(A1,B1)`, `W_beta(A2,B2)`, `W_beta(A1,B2)`, `W_beta(A2,B1)` agree with the corresponding continuous-version entries on a **common fourfold full-measure set**, using explicit quasi-measure-preserving coordinate maps/Fubini and checking every marginal/null-set hypothesis.
2. Derive a right-link retained-sigma-algebra **descent obstruction**: show that the original vacuum being retained-measurable at all right links would force the fourfold Wilson minor to vanish almost everywhere (or find the exact missing compatibility condition). Do not identify full left/right factorization with one-link measurability without an explicit theorem.
3. Only when this original-law nonmeasurability is established, use the existing #5286 iff/positivity theorem to conclude `E_beta^vac > 0` for a fixed finite volume and positive beta. **Finite-volume strict positivity does not provide a volume-independent bound.**
4. Separately, use #5284's **sharp** retained-context witness errors to attempt `E_beta^vac <= Cvac` independent of H, and bound true `A_beta(f) <= Cdrift ||f||²` with `Cdrift` independent of H (or rigorously prove obstruction). Only then instantiate #5290's conditional Gram/Rayleigh estimate.
5. Preserve the independent spacing-scaled generator, compatible adjacent-scale physicality and continuum OS/Wightman mass-gap obligations.

The independent H1-D5 no-go remains in force; the strict-Dobrushin scaling certificate and old sup-width majorants remain refuted as already recorded. **Do not restart the unsuccessful Dobrushin lane.**

This is the exact handoff after merged #5297, not a claim that the positive-beta volume-uniform Yang--Mills mass gap has been proved.
