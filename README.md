# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Theorem-bearing snapshot: 2026-10-08 JST — merged PR #5297, commit `076244eb8b9899c513a9b6fff3e50b6bb1277b37`.**

The active formalization route is **P4: original physical pair-Haar receiver → genuine positive-beta joint posterior → exact Gram/Rayleigh structure → the real SU(2) Wilson crossing obstruction**, without restarting Dobrushin. This repository is a Lean/mathlib *development toward* the four-dimensional Yang--Mills existence and mass-gap problem, **not a completed proof of the continuum mass gap**.

## 0. Current P4 theorem frontier

| Theorem PRs | Established on the authoritative Lean carrier |
| --- | --- |
| #5267--#5273 | Actual right-Krylov and left-three-mode posterior residual Gram matrices, exact Rayleigh identities, mixed-entry control, and **conditional** finite-mode diagonal bounds |
| #5274--#5277 | Frozen beta=0 physical receiver rank one; the fine-beta-zero orbit collapse is a separate statement |
| #5278--#5279 | Original frozen beta=0 posterior fixes every frozen-beta-zero physical receiver; all genuine link losses and associated physical Gram matrices vanish at that endpoint |
| #5280--#5282 | Genuine positive-beta two-drift decomposition; projection drift reduces exactly to one transported constant vacuum under the **original** joint-law `CondExpL2` |
| #5284--#5286 | Sharp retained-sigma measurable-witness Pythagoras; `U_beta(1) = 1/sqrt(W_beta)` joint-a.e.; full-vacuum energy zero iff the original reciprocal-sqrt Wilson density is retained-measurable at every right link |
| #5287, #5289--#5290 | Projection-drift Gram is positive-semidefinite rank at most one; exact combined-input Rayleigh equality and **conditional** mode-count-free physical Gram upper bound |
| #5292 | Exact constant/orthogonal physical input splitting; in the combined constant-orthogonal sector the real physical Gram Rayleigh form **equals** receiver drift (factor 1, not a factor-2 upper bound) |
| #5293--#5294 | Exact factorization of the original physical Wilson-joint 2-by-2 crossing minor; SU(2) symmetric minor reduces to positive spatial half-weights times `1 - crossing(A,B)^2` |
| #5295 | **Concrete** SU(2) one-right-link rotation `R(pi)`: crossing action `2` and kernel `exp(-2 beta) < 1` for every beta>0 and finite even-periodic H; actual one-slab Wilson kernel minor is strictly positive |
| #5296 | Strictly positive **continuous physical top-vacuum** representative gives a continuous joint density `W_{beta,c}`, equal to the original normalized Wilson joint density **pair-Haar almost everywhere**, with an explicit positive pointwise crossing minor |
| **#5297 (latest)** | Strict-minor locus of `W_{beta,c}` is nonempty and open, and has **strictly positive fourfold spatial Haar measure** for each beta>0 and each finite H |

The latest theorem rules out treating the explicit crossing witness as merely an isolated, measure-zero point of the continuous representative. It **does not yet** turn the fourfold positive-measure minor event into a proof that the true posterior vacuum is nonmeasurable with respect to a particular retained-right-link sigma algebra.

**Still open:** the precise fourfold a.e./Fubini lift and right-link descent; a genuinely quantitative **volume-uniform** positive-beta estimate (or obstruction) for the true vacuum posterior energy and receiver drift; spacing-scaled generator control; and the continuum OS/Wightman Yang--Mills mass gap. All positive-beta crossing statements above remain *finite-volume* results. The P3 locality/covariance lane in Sections 3--6 is retained as historical supporting work; repeated Dobrushin reconstruction is deferred.

## 1. Authority and reproducibility

| Item | Verified theorem-bearing checkpoint |
| --- | --- |
| Repository | `itakura-hidetoshi/4d-mass-gap` |
| **Unique authoritative theorem-carrier** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing PR | **#5297 — merged** |
| Latest theorem merge SHA | `076244eb8b9899c513a9b6fff3e50b6bb1277b37` |
| #5297 PR head | `e133452d5f29ea9eab74a23be32b2435b8d1ac5d` |
| PR exact-head CI | [run 37761412979](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37761412979): success |
| Changed Lean job / receipt | 113258448809 / 113259999219: both success |
| Merge SHA CI | [run 37761946518](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37761946518): success |
| Changed Lean build | **10,398 jobs succeeded**; new-file warnings/errors 0; sorry/admit 0 |
| Pinned Lean | `v4.30.0-rc2` |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

GitHub's default `main` **is not theorem authority**. A subsequent README/ROADMAP-only merge changes the authoritative branch HEAD but **does not create a new theorem-bearing baseline**. Before every new theorem PR, freshly inspect the exact theorem-carrier HEAD, read Lean definitions/theorems at that SHA, then inspect docs and the matching exact-head CI receipt. Conversation history is a lower-priority handoff aid.

## 2. Retained finite-volume results and no-go statements

The finite-volume transfer lane still retains the proved lower bounds kappa_12 >= 1/2304 and transfer gap >= 1/3072, with q0 = 3071/3072, under the hypotheses of those theorems. These constants are finite-volume transfer statements, not a continuum physical mass.

H1-D4 remains closed. The old completed H1-D5 whole-operator compatibility is refuted at positive SU(2) coupling and must not be reintroduced under another name.

PR #5207 remains a no-go only for the specific fixed-s > 8 strict-Dobrushin finite-positive-mass scaling certificate. It is not a no-go theorem for every continuum route.

PR #5217 remains a limitation of the old uncorrected sup-width initial majorants. The newer signed L2 route does not repeal that theorem.

## 3. Structural posterior-to-energy chain: closed

PRs #5208--#5212 identify the literal posterior one-link conditional law with the pre-existing joint conditional-expectation projection and extend this to arbitrary finite chronological schedules. For the existing joint Hilbert carrier, stage residual energy is exactly the norm of the corresponding projection residual. Repeated links are allowed; the projections are not assumed to commute.

PRs #5214--#5218 propagate actual posterior variation through prefixes, connect the fixed-color enumerations to the six-color profile, and retain the same-scale centered comparison.

PR #5219 constructs fineFrozenBCF with exactly zero approximation error to the unchanged frozen vector. The orbit uses beta_(n+1), while the final frozen transfer and joint half-density use beta_n. The r = 0 case remains included.

PR #5221 proves the noncommuting projection union bound. In particular the six-color path-loss quantity is controlled by four times the initial one-link residual sum I(f), without identifying noncommuting path loss with total displacement squared.

PRs #5222--#5223 preserve the source-kernel difference signed and prove the exact posterior resampling Dirichlet identities

B_e(x) = (1/2) Q_e(x),

and

I(f_frozen) = (1/12) sum_e Q_e(x).

The factor 1/12 is exact and must be preserved.

## 4. Source-coordinate localization: closed structurally

PR #5224 factors one right-link kernel update into:

- a source-only Wilson tilt depending on one source-right link coordinate;
- an output/half-density factor;
- the unchanged kernel.

The source tilt satisfies the local width bound |tilt - 1| <= exp(2 beta) - 1.

PR #5225 introduces the source-coordinate CondExpL2 projection on the existing pair-Haar L2 space. This projection is not the posterior output projection and not the physical transfer.

For the centered source-coordinate vector C_e^src, the exact signed defect has the form

D_e = [1 - Out_e (1 + AvgTilt_e)] O_x
      - Out_e <C_e^src, Tilt_e>.

The scalar output drift is genuine and cannot be deleted from an individual defect.

## 5. P3-A and seed-distance geometry: closed

PR #5227 defines the actual four-link primary-plaquette seed geometry and the intrinsic seed distance. It proves the near/far partition and shows that seed distance > 2 supplies the distinctness and plaquette-remoteness hypotheses required by the existing posterior covariance theorem.

PR #5228 specializes the #5199 local-factor covariance theorem to the primary seed and rewrites the denominator using the intrinsic seed distance.

PR #5229 proves a volume-independent polynomial shell bound for exact seed-distance shells. The shell size is controlled by a cubic majorant, uniformly in the periodic volume.

PR #5230 sums the seed-distance covariance decay against those polynomial shells and obtains a volume-independent completed covariance mass for the full local factors on the radius-two exterior.

Thus P3-A is closed and the full-local-factor version of the P3-B shell mechanism is already theorem-generated.

## 6. P3-B/P3-C progress through #5235

PR #5231 splits the original squared defect into two explicit nonnegative envelopes:

1. the retained scalar output/half-density drift;
2. the centered source-coordinate contribution, bounded using the existing local source-tilt L2 norm estimate.

PR #5232 proves a stronger structural identity for two signed inputs. In the cross-multiplied contrast, both the common scalar output drift and the common source-tilt mean cancel exactly:

O_v D_x - O_x D_v
  = Out * (O_x <C_v,Tilt> - O_v <C_x,Tilt>).

PR #5233 removes the strictly positive output factor exactly:

Out^(-1) (O_v D_x - O_x D_v)
  = O_x <C_v,Tilt> - O_v <C_x,Tilt>.

No observable is divided by, so zeros of O_x or O_v are harmless. This does not identify the deweighted contrast with the original one-link Dirichlet defect.

PR #5234 factors the full posterior right-target local factor exactly as

fullLocalFactor = boundaryTilt * sourceRightLinkTilt,

where boundaryTilt is independent of the posterior integration variable. The scalar therefore pulls exactly through posterior covariance.

PR #5235 proves the volume-independent bounds

exp(-6 beta) <= boundaryTilt <= exp(6 beta),

boundaryTilt^(-1) <= exp(6 beta),

using the six-touching-plaquette incidence bound and the Wilson-energy width. It then transfers the seed-distance covariance decay to the literal source-only tilt used by the signed joint response:

|Cov(seedLocalFactor, sourceRightLinkTilt)|
  <= exp(6 beta) * covariancePrefactor(s,beta)
     / s^(seedDistance(source)),

for the proved cutoff and remoteness hypotheses. Both the distance > 2 and radius-two-exterior forms are formalized.

## 7. Active P4 mathematical structure and immediate obstruction

Write `V_beta` for the **unchanged physical normalized pair-Haar receiver**, `U_beta` for the genuine half-density isometry, `P_{beta,e}` for the original joint posterior conditional expectation, and `Q_{beta,e} = U_beta^{-1} P_{beta,e} U_beta`. Frozen beta and fine beta in the adjacent-scale right-Krylov orbit must not be conflated.

For a physical input `f`, the actual positive-beta Dirichlet residual and its beta-zero-anchored drift terms are

```text
D_beta(f) = sum_e ||(I-Q_beta,e) V_beta f||^2
A_beta(f) = sum_e ||(I-Q_beta,e)(V_beta f - V_0 f)||^2
B_beta(f) = sum_e ||(Q_0,e - Q_beta,e) V_0 f||^2
E_beta^vac = sum_e ||(I-P_beta,e) U_beta(1)||^2.
```

PR #5280 proves `D_beta(f) <= 2(A_beta(f)+B_beta(f))`. PRs #5281--#5282 give the **exact** rank-one identity

```text
B_beta(f) = inner(unit,f)^2 * E_beta^vac.
```

For `F = sum_i a_i f_i`, #5287/#5289 prove

```text
B_beta(i,j) = inner(unit,f_i)*inner(unit,f_j)*E_beta^vac
a^T B_beta a = inner(unit,F)^2 * E_beta^vac.
```

PR #5290 provides the *conditional* estimate `a^T G_beta a <= 2(Cdrift+Cvac)||F||^2` provided the **original** receiver-drift and vacuum-energy bounds are separately proved. PR #5292 strengthens the constant-orthogonal sector to the **exact** equality `a^T G_beta a = A_beta(F)` whenever `inner(unit,F)=0`; this removes the factor two for that sector only.

For the genuine Wilson density, let `Omega_c` denote the existing everywhere-positive continuous representative of the physical ground-state eigenvector, and `K_beta` the unchanged one-slab Wilson kernel. PRs #5293--#5296 show that

```text
W_{beta,c}(A,B) = ||T_beta||^(-1) Omega_c(A) K_beta(A,B) Omega_c(B)
W_{beta,c} = W_beta               (pair-Haar almost everywhere)
minor(W_{beta,c}) = ||T_beta||^(-2)
                    * Omega_c(A1)*Omega_c(A2)*Omega_c(B1)*Omega_c(B2)
                    * minor(K_beta).
```

For an explicit identity boundary `A` and one-link `R(pi)` updated boundary `B`, #5295 gives `crossing_beta(A,B)=exp(-2 beta)<1`. PR #5296 deduces a strictly positive **continuous-representative** minor. PR **#5297** proves that its strict-minor locus is **open, nonempty and of positive measure in the fourfold spatial Haar product**.

**The next genuine descent obligation** is not another crossing-witness search: it is to transport fourfold a.e. identities for the original normalized Wilson joint law through Fubini and the right-link retained sigma algebra to an *actual* nonmeasurability claim for `U_beta(1)`—or identify a precise obstruction. Only after proving the resulting linkwise statement can #5286 be used to deduce strictly positive original posterior-fiber energy. Strict positivity at fixed finite H must still not be confused with a volume-uniform lower/upper bound.

In parallel, construct retained-measurable local witnesses `g_e` with **summable** original-joint `L2` errors as in #5284, and independently control `A_beta(f)`. No claim of a volume-independent positive-beta bound, a spacing-scaled generator estimate, or a continuum Yang--Mills mass gap follows from the crossing minors.

## 8. Independent adjacent-scale and continuum obligations

Keep these independent of the finite-volume P4 crossing result and the historical P3 route:

- C1: common-marginal physicality / leakage control;
- C2: vector-wise physical transfer / reconstruction commutation;
- C3: weighted beta-increment summability for an explicit beta trajectory;
- compatibility of fixed-natural-time limits as iterates of one limiting discrete-time operator;
- H2: spacing-sensitive physical-time dynamics or generator scaling;
- H3: OS Hamiltonian reconstruction;
- H4: continuum Wightman / energy-momentum spectral mass gap.

Do not revive the refuted whole-operator H1-D5 route to solve C1 or C2.

## 9. Forbidden shortcuts

- Do not apply q0 to |x|; preservation of the non-top sector after absolute value is unproved.
- Do not identify posterior projection, source-coordinate projection, physical transfer, or adjacent-scale coarse physical projection.
- Do not replace joint-a.e. statements by pointwise statements on exceptional fibers.
- Do not infer original posterior one-link nonmeasurability directly from a pointwise or positive-fourfold-Haar crossing minor without the necessary a.e. Fubini/retained-sigma descent.
- Do not infer a volume-uniform positive-beta estimate or continuum mass gap from finite-volume strict crossing positivity.
- Do not infer locality from compactness, BCF density, finite-dimensionality, or positivity alone.
- Do not concatenate the six colors into a single sweep when the theorem treats six sweeps from the same initial vector.
- Do not identify noncommuting path loss with the squared total displacement.
- Preserve the exact 1/6 six-color normalization and 1/12 resampling normalization.
- Do not infer a covariance-to-source-coordinate-norm identity unless it is explicitly proved.

## 10. Restart order

Read the **current P4 proof chain** at the exact authoritative SHA (prefix each filename with `MGAP4D/MathlibAnalytic/`):

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
17. **`PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarContinuousJointCrossingPositiveMeasure.lean`** — latest theorem

For the **historical P3** source-only tilt/covariance lane, refer to #5227--#5235 and:

- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedPolynomialShell.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceMass.lean`
- `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDefectSplit.lean`
- `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateContrast.lean`
- `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDeweightedContrast.lean`
- `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorSourceTiltCovarianceFactorization.lean`
- `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSourceTiltSeedCovarianceDecay.lean`

Keep the exact posterior resampling/energy inputs #5221--#5223 and covariance input #5199 as their own established results.

## 11. Verification discipline

Latest theorem-bearing exact-head receipt:

| Evidence | Value |
| --- | --- |
| PR #5297 validated head | `e133452d5f29ea9eab74a23be32b2435b8d1ac5d` |
| [Changed Lean fast check](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37761412979) | run 37761412979 / job 113258448809 — SUCCESS |
| Matching MCP receipt publisher | job 113259999219 — SUCCESS |
| Build and new-file audit | 10,398 jobs successful; no new warning/error; sorry/admit 0 |
| Theorem-bearing merge | `076244eb8b9899c513a9b6fff3e50b6bb1277b37` |
| [Post-merge exact-SHA CI](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/37761946518) | SUCCESS |

For **theorem-bearing PRs**, inspect *all* changed Lean files, imported APIs and their types, require the matching exact-head Lean job and MCP completion receipt to be green, and only then merge. A receipt does not override a failing Lean job.

For **documentation-only PRs**, verify that the diff contains only `README.md` and `ROADMAP.md`. Do not confuse the resulting docs-only merge SHA with a new mathematical result.

See [ROADMAP](ROADMAP.md) for the staged next obligations.
