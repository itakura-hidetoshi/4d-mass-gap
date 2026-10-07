# MGAP4D

Hidetoshi Itakura's Lean 4 / mathlib development for the four-dimensional Yang--Mills existence and mass-gap program.

**Theorem snapshot: 2026-10-07 JST, through merged PR #5235.**

The current theorem-bearing line has moved beyond the structural posterior-to-joint bridge and into quantitative P3 locality. The formal development now contains:

- the exact posterior fiber -> genuine joint CondExpL2 -> chronological sweep -> stage-residual chain;
- exact representation of the actual frozen Krylov family by bounded-continuous representatives;
- signed one-link Dirichlet identities for the original frozen initial residual energy;
- a primary-plaquette seed-distance geometry and volume-independent polynomial shell count;
- seed-distance posterior covariance decay for the four seed links;
- a volume-independent summed covariance mass for the full local factors;
- an exact source-coordinate decomposition of the signed kernel response, with the scalar output/half-density drift retained;
- an exact cross-multiplied contrast in which the scalar output drift and source-tilt mean cancel;
- exact removal of the positive output factor from that contrast without dividing by either observable;
- exact factorization of the full posterior local factor into a source-independent boundary tilt times the source-only tilt used by the signed joint response;
- volume-independent bounds exp(-6 beta) <= boundaryTilt <= exp(6 beta), hence boundaryTilt^(-1) <= exp(6 beta);
- seed-distance covariance decay transferred to that literal source-only tilt, with only the explicit extra factor exp(6 beta).

The main unresolved P3 step is now narrower: connect the proved source-only posterior covariance decay to the actual frozen centered source-coordinate term, or otherwise obtain a direct distance-sensitive bound on the original resampling Dirichlet contribution Q_e. No complete continuum Yang--Mills measure, physical-time Hamiltonian, or Wightman mass-gap theorem is claimed by this checkpoint.

## 1. Authority and reproducibility

| Item | Current checkpoint |
| --- | --- |
| Repository | itakura-hidetoshi/4d-mass-gap |
| Unique theorem-carrier branch | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing merge | ceb98d0a24fbb132e4519a582d87ac5cf2e86673 |
| Latest theorem-bearing PR | #5235, merged |
| Validated #5235 PR head | 032511aed28fe689b0ebba5b1008639980df9cfe |
| PR Lean Fast Check | run 37581017313, success |
| Actual Changed Lean job | 112660444213, success |
| Matching receipt publisher | 112661593228, success |
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

## 7. Current frontier

The immediate unresolved bridge is **not** the seed geometry and **not** the source-only covariance decay. It is the passage from those proved posterior covariance estimates to the actual frozen source-coordinate / Dirichlet quantity.

The target remains

I_n(f_frozen(n,r,k))
  = (1/12) sum_e Q_(n,e)(x_(n,r,k)),

with a volume-uniform or summable spatial bound sufficient for the existing adjacent-scale tail receivers.

The next model-facing steps are:

- sum the #5235 source-only tilt covariance decay over the already-proved polynomial seed shells;
- construct an exact bridge from the actual frozen signed source response or deweighted cross contrast to a posterior covariance controlled by the seed estimates;
- alternatively derive a direct distance-sensitive estimate for the centered source-coordinate norm or its integrated square;
- return that estimate to the original Q_e sum while keeping the individual-defect output drift unless a proved contrast identity legitimately cancels it;
- control the finite near-link contribution as well as the exterior tail.

A target form such as

4 I_n <= C_(r,k) * rho^D / (1 - rho),   0 <= rho < 1,

remains a goal, not a theorem.

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

For the current P3 frontier, read under MGAP4D/MathlibAnalytic in this order:

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
| Validated #5235 head | 032511aed28fe689b0ebba5b1008639980df9cfe |
| PR Lean Fast Check | run 37581017313, success |
| Actual Changed Lean job | 112660444213, success |
| Matching receipt publisher | 112661593228, success |
| Merge | ceb98d0a24fbb132e4519a582d87ac5cf2e86673 |

For theorem-bearing PRs, inspect all changed Lean files, require success of the actual Lean job, and require a matching exact-head receipt. A successful receipt publisher never overrides a failed Lean job.

For README/ROADMAP-only changes, verify that only those documentation files changed. Do not manufacture theorem CI evidence for a docs-only commit.

See [ROADMAP](ROADMAP.md) for the staged next obligations.
