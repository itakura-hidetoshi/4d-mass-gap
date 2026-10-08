# MGAP4D Roadmap

**Status date: 2026-10-08 JST. Theorem snapshot: through merged PR #5287, merge a5a7c8b58d4b55843393a1ec7e3086d8143b63a2.**

This roadmap separates proved finite-model statements, closed structural bridges, partially closed P3 locality layers, refuted routes, and genuinely open model/continuum obligations. Lean declarations on the theorem-carrier are the mathematical source of truth.

## 0. Authority checkpoint

| Item | Checkpoint |
| --- | --- |
| Unique theorem-carrier | formal/real-hilbert-uniform-coercive-strong-limit |
| Latest theorem-bearing merge | a5a7c8b58d4b55843393a1ec7e3086d8143b63a2 |
| Latest theorem-bearing PR | #5287, merged |
| Validated #5287 head | 3d99456a10a8b0d6d5e9a2128eba2f5aa9517a81 |
| Lean / mathlib | v4.30.0-rc2 / 5450b53e5ddc75d46418fabb605edbf36bd0beb6 |

Authority order:

1. fresh exact theorem-carrier SHA;
2. formal Lean artifacts at that SHA;
3. README / ROADMAP;
4. matching exact-head CI evidence;
5. history or conversation memory.

The default main branch is not theorem authority.

## 0A. ACTIVE P4: genuine posterior Gram and joint-vacuum energy (non-Dobrushin)

The later theorem-bearing progression has moved beyond the historical P3 checkpoint:

| PRs | Formalized finite-volume result |
| --- | --- |
| #5267--#5273 | Original right-Krylov / left-three-mode residual Gram, exact Rayleigh identities and conditional finite-mode diagonal criterion |
| #5274--#5277 | Frozen beta=0 physical receiver rank one; fine-beta=0 orbit collapse remains a separate assumption |
| #5278--#5279 | Original frozen beta-zero posterior fixes every physical receiver; all genuine link losses and physical residual Gram entries are zero |
| #5280 | Exact positive-beta D_beta(f) <= 2(A_beta(f)+B_beta(f)) using physical receiver drift and original posterior projection drift |
| #5281 | B_beta(f)=inner(unit,f)^2 * sum_e ||1-Q_beta,e 1||^2; no link-cardinality factor |
| #5282 | B_beta(f)=inner(unit,f)^2 * sum_e ||(I-P_beta,e) U_beta(1)||^2 under the original ground-state joint law |
| #5284 | Sharp retained-context joint-L2 Pythagoras and no-link-count witness bound for the same original posterior vacuum |
| #5285 | U_beta(1)=1/sqrt(W_beta) joint-a.e., with W_beta the original normalized Wilson joint density, and isometric pair-Haar witness-error equality |
| #5286 | Full-link vacuum energy zero iff inverse sqrt Wilson density is retained-measurable for ALL original right links; conditional strict positivity from one nonretained link |
| #5287 | Exact positive-beta projection-drift Gram B_beta(i,j)=inner(unit,f_i)*inner(unit,f_j)*E_beta_vac; positive semidefinite, rank at most one, zero on orthogonal physical families |

**OPEN active targets:** a positive-beta volume-uniform bound (or precise obstruction) for the actual physical receiver drift A_beta(f) and the one-vacuum joint posterior-fiber variance E_beta_vac. PR #5284 supplies a sharp local-witness interface; #5285 supplies the actual Wilson density; #5286 is a CONDITIONAL vanishing obstruction and does NOT prove nonmeasurability for all beta>0; #5287 closes only the outer-product structure of the projection-drift Gram. Next develop an exact Rayleigh-level receiver-drift composition, then use quantitative volume-uniform bounds ONLY after they are proved. Spacing-scaled generator convergence and continuum Yang--Mills mass gap remain OPEN.

Do not restart Dobrushin by default. The exact frozen beta-zero vanishing is not a positive-beta or continuum mass-gap statement.

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

## 2. P3 — quantitative locality of the actual initial residual sum

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
- Do not infer locality from compactness, BCF density, finite-dimensionality or positivity.
- Do not infer hard support for the positive-depth frozen orbit.
- Do not concatenate the six colors into one sweep when the theorem treats six sweeps from the same initial vector.
- Do not replace noncommuting path loss by squared total displacement.
- Preserve the exact 1/6 six-color normalization and 1/12 resampling normalization.
- Do not delete the scalar output drift from an individual defect merely because the cross contrast cancels it.
- Do not identify posterior covariance with ||C_e^src||_2 without an explicit theorem.
- Preserve the distinction between beta_(n+1) in the orbit and beta_n in the final frozen transfer / joint law.

## 8. Source-level handoff

For the current P3 frontier, read in this order:

1. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedDistance.lean
2. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceDecay.lean
3. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedPolynomialShell.lean
4. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSeedCovarianceMass.lean
5. MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateProjection.lean
6. MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateL2.lean
7. MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDefectSplit.lean
8. MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateContrast.lean
9. MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateDeweightedContrast.lean
10. MGAP4D/MathlibAnalytic/PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorSourceTiltCovarianceFactorization.lean
11. MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPosteriorSourceTiltSeedCovarianceDecay.lean

Underlying inputs:

- #5199 posterior canonical spatial covariance decay;
- #5223 exact resampling Dirichlet identity;
- #5221 noncommuting projection union bound;
- #5219 exact frozen BCF representation.

Current P4 source handoff (all under MGAP4D/MathlibAnalytic):

1. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGramDiagonalRayleighCriterion.lean
2. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFrozenZeroAllLinkVanishing.lean
3. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredDrift.lean
4. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredProjectionRankOne.lean
5. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarBetaZeroAnchoredVacuumJointVariance.lean
6. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumRetainedWitnessPythagoras.lean
7. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumWilsonDensityHaarWitness.lean
8. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarVacuumZeroIffRetainedWilson.lean
9. PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveBetaProjectionDriftRankOneGram.lean

The preceding seed/source-only-tilt list belongs to the historical P3 route.

## 9. Verification evidence

Latest theorem evidence:

| Evidence | Value |
| --- | --- |
| Validated #5287 head | 3d99456a10a8b0d6d5e9a2128eba2f5aa9517a81 |
| PR Lean Fast Check | run 37744875925, success |
| Actual Changed Lean job | 113203872566, success |
| Matching receipt publisher | 113205336944, success |
| Merge | a5a7c8b58d4b55843393a1ec7e3086d8143b63a2 |

For theorem-bearing PRs:

- inspect all changed Lean files, not only the reported error line;
- require the actual Changed Lean job to succeed;
- require a matching exact-head receipt;
- do not weaken theorem assumptions, linting or tests to obtain GREEN;
- do not treat a successful receipt publisher as overriding a failed Lean job.

For docs-only changes, verify the diff is documentation-only and do not manufacture theorem CI evidence.

## 10. Immediate next milestone

**Build summable original-Wilson retained-link witnesses and a receiver-drift estimate, then connect the exact rank-one projection-drift Gram to physical Rayleigh forms without Dobrushin.**

The #5281--#5282 identity isolates the real analytic difficulty:

    B_beta(f) = inner(unit,f)^2
                * sum_e ||(I-P_beta,e) U_beta(1)||^2,

with the ORIGINAL joint conditional expectation P_beta,e and true half-density U_beta. This is an exact equality, not a volume-uniform estimate.

PR #5284 shows the vacuum loss is no greater than the sum of squared errors of retained-link measurable witnesses g_e, with sharp constant 1 and a genuine orthogonal remainder. PR #5285 identifies U_beta(1) joint-a.e. with 1/sqrt(W_beta), with W_beta retaining the actual top eigenvector, Wilson kernel, and transfer-norm normalization. PR #5286 gives an exact vanishing criterion: all off-target retained sigma-algebras must see the inverse-sqrt Wilson density; nonmeasurability at any link conditionally forces strict positivity. PR #5287 proves every projection-drift Gram entry has rank-one form inner(unit,f_i)*inner(unit,f_j)*E_beta_vac.

Next construct actual g_e and show SUMMABLE approximation error in spatial volume (or a rigorous obstruction), using the true Wilson density rather than surrogate Haar laws. Independently control A_beta(f), the genuine physical receiver drift from beta=0. Preserve a distinct fine beta(n+1) orbit and frozen beta(n) posterior; do not replace full-link sums by a crude link count.

The #5287 outer-product structure already treats the projection-drift Gram without a dimension/mode-count factor. Formalize its exact Rayleigh form and connect it to the remaining physical receiver drift; apply #5273 only where its conditional diagonal-to-Rayleigh bound is genuinely needed. No positive-beta volume-uniform bound is currently proved. The spacing-scaled generator gap, OS continuum reconstruction, and Yang--Mills mass gap stay OPEN.
