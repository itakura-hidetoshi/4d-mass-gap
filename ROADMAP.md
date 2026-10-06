# MGAP4D Roadmap

**Status date: 2026-10-07 JST. Theorem snapshot: through merged PR #5225, merge `98daa981bbf9d175ea60618cce77c1ccdb6c075d`.**

This roadmap separates proved finite-model statements, closed structural bridges, refuted routes, and genuinely open model/continuum obligations. Lean declarations are the mathematical source of truth.

## 0. Authority checkpoint

| Item | Checkpoint |
| --- | --- |
| Unique theorem-carrier | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing merge | `98daa981bbf9d175ea60618cce77c1ccdb6c075d` |
| Latest theorem-bearing PR | #5225, merged |
| Validated #5225 head | `d078f458b141ded5b8bc4de7aa8f4ddd51b823f8` |
| Lean / mathlib | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

Authority: fresh theorem-carrier SHA -> formal Lean artifacts -> README/ROADMAP -> exact-head CI evidence -> history. The default `main` branch is not theorem authority.

## 1. Closed chain — do not reconstruct

The structural posterior-to-energy bridge is now closed:

| Range | Established result |
| --- | --- |
| #5208--#5212 | Literal posterior fiber law -> genuine joint CondExpL2 -> arbitrary chronological schedules -> exact stage-residual energy |
| #5214--#5218 | Actual prefix variation propagation, fixed-color enumeration, six-color (1/6) profile, (L^2) stability, continuous scalar majorants, left-centered comparison |
| #5219 | `fineFrozenBCF` exactly equals the actual frozen vector; approximation error zero |
| #5220 | One-link (L^2) envelope including half-density variation |
| #5221 | Noncommuting projection union bound; (mathcal E(f)le4I(f)) |
| #5222 | Signed link-local residual energy and exact set/complement splitting |
| #5223 | Exact posterior Dirichlet identity (B_e=rac12Q_e) |
| #5224 | Exact one-source-link Wilson tilt factorization |
| #5225 | One-source-coordinate pair-Haar (L^2) projection and centered signed-response decomposition, retaining output drift |

The actual frozen convention remains fixed:
[
x_{n,r,k}=widehat T_{n+1,eta_{n+1}}^rphi_{n+1,k},
]
while the final frozen transfer and joint half-density use (eta_n). Keep (r=0).

## 2. P3 — quantitative locality of the actual initial residual sum: OPEN

The main object is
[
I_n(f^{frozen}_{n,r,k})
=rac16sum_e|(I-P_{n,e})f^{frozen}_{n,r,k}|_2^2
=rac1{12}sum_eQ_{n,e}(x_{n,r,k}).
]

#5222 preserves signed cancellation link by link. #5224 shows that the source-dependent update factor sees only (y_R(e)). #5225 projects the actual signed kernel-weighted row onto precisely that one source coordinate.

What is **not** yet proved is that the projected signed row becomes small with spatial separation. The kernel-weighted row itself may remain nonlocal. Therefore the next theorem must use the actual model geometry/dynamics, not density or compactness alone.

### P3-A. Identify the geometric support/distance interface

For fixed (r,k), define the relevant near-link set (S_{n,r,k}(D)) from the actual three-mode seed/orbit geometry. Prove the exact link-distance statements needed to invoke existing local-factor/covariance machinery.

**Acceptance:** no invented support for an (L^2) representative; every distance statement is about concrete Wilson/link data already constructed.

### P3-B. Exterior signed-coordinate estimate

For (e
otin S_{n,r,k}(D)), bound the actual centered coordinate term
[
|Pi_e^{src}(J(cdot,z)x_{n,r,k}-O_{n,r,k}(z))|_2
]
or its integrated squared contribution by a decaying function of distance.

The #5199 covariance theorem may be used only where its distinctness, plaquette-remoteness, cutoff and observable hypotheses match. Its (sge1) theorem gives genuine decay for (s>1). Do not silently replace it by the strict uniform-Dobrushin (s>8) hypotheses.

**Acceptance:** a theorem-generated exterior contribution with all constants/cutoffs explicit and no volume-cardinality loss hidden in notation.

### P3-C. Retained scalar output drift

#5225 proves that even if the centered source-coordinate term vanishes, the defect still contains
[
[1-operatorname{Out}_e(1+operatorname{AvgTilt}_e)]O_x.
]

Control this term from the actual half-density/output structure. Do not delete it by a source-independence assumption.

**Acceptance:** an integrated bound on the drift term under the original posterior/joint laws, compatible with the same distance decomposition.

### P3-D. Sum near and exterior contributions

Combine the exact (1/12)-normalized Dirichlet representation with P3-B/P3-C and prove, for each fixed (r,k), a bound of the form
[
4I_n(f^{frozen}_{n,r,k})
le C_{r,k}rac{ho^{D_{n,r,k}}}{1-ho},
qquad 0leho<1,
]
or another summable bound sufficient for the existing adjacent-tail receiver.

**Acceptance:** volume-uniform or explicitly summable control of the **whole** initial residual sum. Exterior decay alone is insufficient if near terms remain uncontrolled.

## 3. Independent adjacent-scale obligations

### C1. Common-marginal physicality — OPEN

The posterior/source-coordinate projections are not the adjacent-scale coarse physical projection. Prove the required leakage bound for the reconstructed candidate:
[
|Y_n-P_n^{phys}Y_n|^2
]
or the exact equivalent field required by the existing receiver.

Do not infer physicality from posterior averaging or membership in the same Hilbert space.

### C2. Physical transfer / reconstruction commutation — OPEN

For each fixed finite (r,k), control the actual mismatch between fine transfer followed by reconstruction and coarse physical transfer on the reconstructed orbit. A summable vector-wise bound is sufficient; whole-space operator-norm convergence is not required.

Do not revive the refuted H1-D5 whole-operator compatibility.

### C3. Weighted beta trajectory — OPEN INPUT

Use the existing same-volume normalized physical-transfer beta-response coefficient and prove summability for an explicit trajectory:
[
C_{norm}(n,eta_n,eta_{n+1})|eta_{n+1}-eta_n|.
]

Small unweighted increments alone are insufficient.

## 4. H1-C3 closure and later physical layers

Once P3, C1, C2 and C3 are supplied, existing receivers can convert the finite reconstruction/orbit mismatch into fixed-natural-time Cauchy/strong limits and a nonzero time-zero excitation under their hypotheses.

Still separate:

1. **Limiting discrete-time operator:** fixed-(m) limits do not automatically define compatible iterates of one operator.
2. **H2 physical time:** if (a_n	o0) while a fixed (q_0<1) controls the sector, then (q_0^{lfloor t/a_nfloor}	o0) for (t>0). A nontrivial strongly continuous semigroup needs scale-sensitive operator/generator data and physical time identification.
3. **H3 OS Hamiltonian:** construct/identify the physical Hilbert space and generator with the required positivity/self-adjointness/vacuum properties.
4. **H4 Wightman/energy-momentum mass gap:** verify the continuum reconstruction and spectral statement for the intended Yang--Mills theory.

## 5. Closed no-go routes

### N1. Old completed H1-D5

At positive SU(2) coupling the old completed compatibility forces rank-one behavior contradicted by the constructed two-mode sector. Do not restore it as vacuum/top alignment, exact completed cross-scale transfer compatibility, or an equivalent OS-boundary/physical-pair transfer identity.

### N2. #5207 strict-Dobrushin finite-positive-mass certificate

For fixed (s>8), the existing certificate confined to the canonical closed strict-Dobrushin interval cannot simultaneously have (a_n	o0) and
[
(1-aralpha(s,eta_n))/a_n	o m,qquad 0<m<infty.
]

This is a no-go for that certificate, not for all continuum routes and not a proof of a critical point outside the interval.

### N3. #5217 old sup-norm-width majorant family

The limitation of the old uncorrected uniform initial-width (2|O|_infty) majorant remains valid. The newer signed (L^2) route does not repeal that theorem.

## 6. Forbidden shortcuts

- Do not apply the non-top contraction (q_0) to (|x|); non-top preservation after absolute value is unproved.
- Do not identify posterior projection, source-coordinate projection, physical transfer and coarse physical projection.
- Do not replace a joint-a.e. identity by a pointwise identity on exceptional fibers.
- Do not infer locality from BCF density, finite-dimensionality, compactness or positivity of the half-density.
- Do not concatenate the six colors into one sweep when the theorem treats six sweeps starting from the same (f).
- Do not replace path loss by the squared total vector displacement for noncommuting projections.
- Preserve the (1/6) six-color normalization and the exact (1/12) resampling normalization.

## 7. Source-level handoff

Read in this order, all under `MGAP4D/MathlibAnalytic/`:

1. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateProjection.lean`
2. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceCoordinateL2.lean`
3. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSourceLocalTilt.lean`
4. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointResamplingDirichlet.lean`
5. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointLinkLocalEnergy.lean`
6. `PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointSweepL2Envelope.lean`
7. `RealHilbertProjectionSweepUnionBound.lean`

Then trace backward through #5212 stage energy, #5211 finite schedule, #5210 CondExpL2 and #5208--#5209 fiber bridges. For model locality also inspect #5199 and the existing adjacent frozen-Krylov tail receiver.

## 8. Verification and Lean lessons

Latest theorem evidence:

| Evidence | Value |
| --- | --- |
| Validated #5225 head | `d078f458b141ded5b8bc4de7aa8f4ddd51b823f8` |
| PR Lean Fast Check | run `37546090512`, success |
| Actual Changed Lean job | `112550339294`, success |
| Matching receipt publisher | `112551903523`, success |
| Merge | `98daa981bbf9d175ea60618cce77c1ccdb6c075d` |

#5225 debugging reinforced several pinned-Lean rules: declaration names are fully namespace-qualified; use pinned `Real.continuous_exp.comp` rather than guessed field notation; normalize real scalar inner products explicitly before ring reasoning; use the correct arity of absolute-value triangle lemmas; and remove tactics after a preceding tactic has already closed the goal. The source-coordinate measurable-space definition is reducible to support elaboration.

For theorem-bearing PRs, inspect all changed source files and require the actual Lean job plus a matching exact-head receipt. A successful receipt publisher never overrides a failed Lean job. Do not weaken assumptions, linting or tests to obtain GREEN.

For README/ROADMAP-only updates, verify the two-file diff; no redundant theorem CI claim is needed.

## 9. Immediate next deliverable

**Construct P3-B/P3-C on the actual frozen family:** a distance-sensitive bound for the centered one-source-coordinate response together with the retained scalar output drift, then sum it through the exact (1/12) Dirichlet representation.

Everything through the structural P1/P2 bridge is already available. Do not restart posterior normalization, finite schedules, noncommuting sweep comparison, exact BCF construction, signed link energy, or source-coordinate localization.
