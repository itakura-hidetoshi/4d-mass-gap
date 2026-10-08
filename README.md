# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Theorem snapshot: 2026-10-08 JST, through merged PR #5287, merge a5a7c8b58d4b55843393a1ec7e3086d8143b63a2.**

The theorem-bearing development has advanced beyond the historical #5235 P3 locality checkpoint. The active route is P4: **actual physical posterior Gram and genuine posterior-fiber energy, without Dobrushin reconstruction**.

## 0. Current P4 results

- **#5267--#5273:** original right-Krylov and left-three-mode posterior residual Gram matrices, exact Rayleigh identities, off-diagonal control, and conditional diagonal-to-Rayleigh bounds. A positive-beta volume-uniform diagonal constant is NOT proved.
- **#5274--#5277:** frozen beta=0 physical receiver is rank one; fine-beta=0 right orbit collapse is a DIFFERENT condition; beta-zero Gram reduction is one-dimensional.
- **#5278--#5279:** the original frozen beta-zero posterior fixes every physical receiver, making the actual full-link residual sum and all physical-family Gram entries EXACTLY zero, without a fine-beta=0 assumption.
- **#5280:** genuine positive-beta posterior residuals split into true receiver drift A_beta(f) and true posterior projection drift B_beta(f), with D_beta(f) <= 2(A_beta(f)+B_beta(f)) and no explicit spatial-link cardinality multiplier.
- **#5281:** B_beta(f) = inner(unit,f)^2 * sum_e ||1-Q_beta,e 1||^2; orthogonal physical inputs have B_beta(f)=0.
- **#5282:** B_beta(f) = inner(unit,f)^2 * sum_e ||(I-P_beta,e) U_beta 1||^2 on the ORIGINAL ground-state joint law, using the existing half-density isometric equivalence.
- **#5284:** sharp L2 retained-sigma-algebra witness Pythagoras for the genuine vacuum, with sum_e ||(I-P_beta,e)U_beta 1||^2 <= sum_e ||U_beta 1 - g_e||^2 and exact orthogonal remainder. Existence of volume-uniform local witnesses is OPEN.
- **#5285:** U_beta 1 = 1 / sqrt(W_beta) joint-a.e. for the actual normalized Wilson density W_beta; witness approximation errors transport isometrically back to pair Haar, without two-sided weight constants.
- **#5286:** the full-link vacuum posterior energy vanishes iff the literal inverse-sqrt Wilson density is retained-a.e.-measurable for every original right link. Failure at one link gives positive energy conditionally; positive-beta failure of measurability itself is NOT established.
- **#5287:** the genuine positive-beta projection-drift Gram on ANY finite physical family has EVERY entry B_beta(i,j) = inner(unit,f_i) * inner(unit,f_j) * E_beta_vac. It is positive semidefinite, rank at most one, and zero on families orthogonal to the constant mode.

These are exact finite-volume statements. **OPEN**: positive-beta volume-uniform control of A_beta(f) and the canonical vacuum joint posterior-fiber variance, spacing-scaled physical-time generator gap, and continuum Yang--Mills mass gap. Beta=0 exact vanishing does NOT establish any positive-beta/continuum gap. Dobrushin remains deferred.

Sections 3--6 below preserve the older P3 locality/covariance route as historical and supporting work, not the current frontier.

## 1. Authority and reproducibility

| Item | Current checkpoint |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing merge | a5a7c8b58d4b55843393a1ec7e3086d8143b63a2 |
| Latest theorem-bearing PR | #5287, merged |
| Validated #5287 PR head | 3d99456a10a8b0d6d5e9a2128eba2f5aa9517a81 |
| PR Lean Fast Check | run 37744875925, success |
| Actual Changed Lean job | 113203872566, success |
| Matching receipt publisher | 113205336944, success |
| Pinned Lean | v4.30.0-rc2 |
| Pinned mathlib | 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

The default branch main is **not theorem authority**. Re-observe the theorem-carrier before continuing.

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean theorem artifacts at that SHA;
3. README / ROADMAP;
4. matching exact-head CI evidence;
5. conversation history or prior summaries.

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

## 7. Current frontier: positive-beta actual posterior-fiber energy

For the original physical receiver V_beta(f) and original transported joint posterior Q_beta,e:

    D_beta(f) = sum_e ||(I-Q_beta,e) V_beta(f)||^2
    A_beta(f) = sum_e ||(I-Q_beta,e)(V_beta(f)-V_0(f))||^2
    B_beta(f) = sum_e ||(Q_0,e-Q_beta,e) V_0(f)||^2

#5280 proves D_beta <= 2(A_beta+B_beta). #5281--#5282 prove exactly

    B_beta(f) = inner(unit,f)^2
                * sum_e ||(I-P_beta,e) U_beta(1)||^2.

#5284 makes E_beta_vac a sharp retained-link local-witness approximation problem. #5285 supplies the literal Wilson-density inverse-sqrt representative of that vacuum; #5286 characterizes its exact zero-energy measurability obstruction. #5287 upgrades B_beta from a DIAGONAL reduction to the full positive-semidefinite rank-one outer-product Gram on arbitrary finite physical families. For constant-orthogonal f, B_beta(f)=0 and the ENTIRE projection-drift Gram vanishes, but the separate receiver drift A_beta(f) is still open.

**Next P4 proof obligation:** construct original-joint retained-measurable local witnesses g_e with SUMMABLE approximation errors for U_beta(1) = 1/sqrt(W_beta), or exhibit a rigorous obstruction to such control at positive beta. Independently bound the actual physical receiver drift A_beta(f). Use genuine Wilson kernel/top-vacuum dependence and original CondExpL2, NOT surrogate laws, crude link counting, or repeated Dobrushin. The #5287 rank-one Gram gives a mode-count-free structure for the projection drift; a Rayleigh-level composition with the true receiver drift is the next formal interface. No volume-uniform bound, spacing-scaled generator gap, or continuum Yang--Mills mass gap is thereby proved.

The older P3 seed-distance/source-only-tilt route is preserved in the preceding historical sections under its original hypotheses.

## 8. Independent adjacent-scale and continuum obligations

Keep these separate from P3:

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
- Do not infer locality from compactness, BCF density, finite-dimensionality, or positivity alone.
- Do not concatenate the six colors into a single sweep when the theorem treats six sweeps from the same initial vector.
- Do not identify noncommuting path loss with the squared total displacement.
- Preserve the exact 1/6 six-color normalization and 1/12 resampling normalization.
- Do not infer a covariance-to-source-coordinate-norm identity unless it is explicitly proved.

## 10. Restart order

For the CURRENT P4 frontier, read under MGAP4D/MathlibAnalytic in this order:

1. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGramDiagonalRayleighCriterion.lean
2. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFrozenZeroAllLinkVanishing.lean
3. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredDrift.lean
4. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredProjectionRankOne.lean
5. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredVacuumJointVariance.lean
6. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumRetainedWitnessPythagoras.lean
7. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness.lean
8. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumZeroIffRetainedWilson.lean
9. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaProjectionDriftRankOneGram.lean

For the HISTORICAL P3 locality route, read in this order:

1. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance.lean
2. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay.lean
3. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedPolynomialShell.lean
4. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceMass.lean
5. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateL2.lean
6. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDefectSplit.lean
7. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateContrast.lean
8. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDeweightedContrast.lean
9. PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorSourceTiltCovarianceFactorization.lean
10. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSourceTiltSeedCovarianceDecay.lean

For the underlying covariance input also inspect #5199. For the exact energy receiver trace backward through #5223, #5222, #5221 and #5212.

## 11. Verification discipline

Latest theorem evidence:

| Evidence | Value |
| --- | --- |
| Validated #5287 head | 3d99456a10a8b0d6d5e9a2128eba2f5aa9517a81 |
| PR Lean Fast Check | run 37744875925, success |
| Actual Changed Lean job | 113203872566, success |
| Matching receipt publisher | 113205336944, success |
| Merge | a5a7c8b58d4b55843393a1ec7e3086d8143b63a2 |

For theorem-bearing PRs, inspect all changed Lean files, require success of the actual Lean job, and require a matching exact-head receipt. A successful receipt publisher never overrides a failed Lean job.

For README/ROADMAP-only changes, verify that only those documentation files changed. Do not manufacture theorem CI evidence for a docs-only commit.

See [ROADMAP](ROADMAP.md) for the staged next obligations.
