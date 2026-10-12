# MGAP4D — formalization roadmap

**Status: 2026-10-12 JST. Latest theorem-bearing [PR #5480 (P4-Q2-DZ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5480) is MERGED at `d4674e05b4ce1a21ffcdffce42b7de4f5a55df7c`. DY #5478 and DW/DX remain merged prerequisites.**

**Current theorem achievement:** DV full original Wilson Riesz quadratic coercivity, DW true Loewner and separate D12 bilateral comparison, DX boundedly invertible original orthogonal restriction with real spectrum in `[κ_R,12]`, and **DY typed original DQ/DF finite-volume mass/variance coefficient; DZ restores the literal factor 12 from normalized Haar reference to the unnormalized ORIGINAL Wilson Riesz sum with improved same-witness whole-L², Loewner and anti-Lipschitz estimates**. DU separately proves the normalized physical D12 restricted gap.

**Main unresolved scientific target:** control the dependence of the physically relevant quantities on spatial volume `H`, coupling/scales and the actual original-Wilson fine/frozen Krylov family, then establish actual cross-scale reconstruction, nontrivial continuum physical time and a **positive continuum Yang–Mills mass gap**. No such continuum result is claimed.

Read [README.md](README.md) for definitions, exact Wilson-versus-Haar normalization, core theorem, and reproduction command.

## 0. Authority, environment, and current evidence

| Field | Verified checkpoint |
| --- | --- |
| Only theorem-authoritative repository / branch | `itakura-hidetoshi/4d-mass-gap` / `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing merged PR | [#5480](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5480), merge SHA `d4674e05b4ce1a21ffcdffce42b7de4f5a55df7c` |
| Exact-tested PR #5480 source HEAD | `b057e2e618de7597478b909a85807839ed824ff8` |
| Lean / mathlib | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact-source-head CI | [#38230569714](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38230569714), SUCCESS |
| Changed Lean / MCP receipt jobs | `114748729543` / `114750270625`, both SUCCESS |
| Build and diagnostics | **9533/9533**, **DZ changed-file errors/warnings 0**, static audit passed. `#print axioms`: standard Lean axioms plus inherited original color-cardinality, incident-plaquettes-cardinality and other-axis-cardinality `native_decide` dependencies; no NEW axiom declarations and no `sorryAx` in final build. Historical DV has four warnings. |

A later **docs-only merge will move the current canonical branch HEAD** beyond the SHA shown above, but it does not alter the #5480 theorem-bearing result. Observe the branch's fresh exact HEAD for each new PR. GitHub's default `main` is not the theorem authority.

## 1. Proof status matrix

| Proof gate / lane | Actually proved in the authoritative branch | What is still open |
| --- | --- | --- |
| **P4-F1/F2/F3** | **CLOSED**, #5299–#5302: original four-crossing a.e. lift and retained-sigma fiber descent; `E_vac(beta,H)>0` for genuine finite H, `beta>0`. | Strict pointwise-in-H positivity is not an H-uniform lower bound. |
| **P4-Q1** | Fixed-H quantitative Wilson vacuum witnesses #5303–#5309; `E_vac(beta,H) ≤ |E_H| (exp(16 beta)-1)^2` in the verified regime. | Remove/prove control of `|E_H|`; no continuum control. |
| **P4-Q2 signed uncentered Krylov** | #5310–#5326: physical fine/frozen receiver, signed original posterior covariance and two-copy resampling identity, genuine per-link `W×M` oscillation budget. | Uniform signed Gram row / `ℓ²` operator control; spatial tail or cancellation estimates — **OPEN**. |
| **P4-Q2 original full-`L²` Wilson forms** | #5395–#5427: original physical bounded core, dense extension and self-adjoint `AW`; #5473–#5476 add quadratic, Loewner, bilateral D12 comparison and restricted spectral band. | Uniformity and continuum OPEN. |
| **P4-Q2 qualitative full-`L²` kernel** | **CLOSED** at **#5440 / CO**: `ker(AW)=V_constants`, by real clipping/Markov contraction and a.e. constant gluing; #5441 physical mass floor. | **Not** the quantitative spectral lower estimate (supplied later by DV). Do not call CO's former CL obstruction currently open. |
| **P4-Q2 genuine pair-Haar L²** | #5442–#5455: actual CR coordinate projections, exact independent Haar factorization, commutation for these projections, Efron–Stein and global-mean Poincaré. | Never transpose pair-Haar commutation to noncommuting interacting Wilson conditional projections. |
| **P4-Q2 Wilson / Haar physical comparison** | #5456–#5467: real original Wilson / pair-Haar finite-volume variance sandwich, positive original twelve-color Haar mass floor, actual right/left fiber-to-CR defect identities and DP reference lower bound. | Constants are finite-H and may depend on beta/rank. |
| **P4-Q2 normalized→physical gap** | **#5468–#5472 CLOSED**: DQ true all-coordinate Haar floor; DR physical variance; DS full-`L²` E12 coercivity; DT D12 Loewner; DU positive real spectrum of genuine D12 restriction. | D12 is NOT AW; no H-/spacing-uniform spectrum gap. |
| **P4-Q2 original Wilson Riesz quantitative gap** | **DV #5473, DW #5475, DX #5476, DY #5478, DZ #5480 CLOSED**: original AW whole L², Loewner/D12 comparison, inverse/spectral band, explicit DQ/DF m,M witness, and **exact 12-fold normalization recovery with improved same-witness L², Loewner and anti-Lipschitz**. | Genuine H-/spacing-uniform gap and Yang–Mills continuum mass gap remain OPEN. |
| **C1 / C2 / C3** | Previous conditional adjacent-scale interfaces and finite-H components. | Actual common-marginal physicality; vector-wise fine→coarse compatibility; explicit summable beta trajectory — **OPEN**. |
| **H2 / H3 / H4** | Finite-H transfer and spectral infrastructure under precise hypotheses. | Spacing-scaled strongly continuous physical evolution, OS Hamiltonian, continuum Wightman/Yang–Mills mass gap — **OPEN**. |

Do not collapse independent lanes merely because both appear in the P4-Q2 proof chronology: the finite-volume signed uncentered Krylov Gram, `D12`, and original Haar-reference `AW` have **different definitions and proof obligations**.

## 2. Newly closed chain — original Wilson Haar-reference Riesz quantitative coercivity

### 2.1 Definitions and immutable normalization

At the original finite Wilson spatial lattice (with the Lean hypotheses `0 < N`, `0 ≤ beta`), set:

```text
HW       = actual original physical Wilson ground-state joint L²;
V        = intrinsic Wilson constant-line subspace;
Pconst   = orthogonal projection of HW onto V;
AW       = original positive self-adjoint Haar-reference Riesz operator (BY);
QW(x)    = inner_R (AW x) x; continuous original unnormalized Haar sum (BX);
D12      = true physical normalized twelve-color conditional-projection Gram (CA);
E12(x)   = inner_R (D12 x) x = normalized physical 12-color energy;
HaarNorm = (1/12) * (original twelve-color Haar reference SUM);
muPair   = actual independent pair-Haar law, distinct from original muWilson.
```

CA/BZ proved `0 ≤ AW ≤ 12 • D12`; **DV supplies the independent original quadratic lower bound and DW #5475 separately proves `κ_R • D12 ≤ AW`** using BF's true physical `E12(x) ≤ ‖x-Pconst(x)‖²`. The resulting finite-volume bilateral comparison concerns two DISTINCT operators.

### 2.2 Genuine factor chain and its constant

The sequence now formally verified is:

```text
CP/DG        Original finite-volume Wilson Haar link-fiber mass floor m(H,N,beta)>0
CR–DC        True pair-Haar coordinate projections + global-mean Efron–Stein
DE/DF        Actual Wilson/pair-Haar squared-deviation and variance comparison
DK–DP        Genuine left+right Wilson Haar fiber variances = CR L² defects
DQ           Normalized original 12-color Haar reference >=
             [m exp(-32 beta)/(12 * spatialLinkCard)] * all CR defects
DR intermediate (re-expressed in DV):
             Normalized original Haar reference >= positive * Wilson variance
DV           Unnormalized original real Haar reference >=
             min(k,1) * genuine Wilson variance (bounded original core)
BR/CL/DS     Original concrete-to-physical L² quotient and centered Hilbert estimate
BW/BX        Dense original bounded core + continuous full physical joint L² quadratic
DV FINAL     ∃ kappa_R>0, ∀ x:HW,
             kappa_R * ||x-Pconst(x)||² <= QW(x)
```

The **finite-volume** witness for the intermediate bound may be chosen conservatively as

```text
a(H,N,beta) = m(H,N,beta) * exp(-32 beta) / (12 * spatialLinkCard(H))
b(H,N,beta) = M(H,N,beta) + 1
k(H,N,beta) = a(H,N,beta) / b(H,N,beta) > 0
kappa_R(H,N,beta) = min(k(H,N,beta), 1) > 0 .
```

Here `M` is DF's genuine Wilson/pair-Haar variance **upper-comparison** constant. Read the actual DQ, DF and DV theorem statements for exact typed witnesses: this display is an explanatory finite-volume formula, **not a claimed optimized coefficient**. No lower bound uniform over `H` for `m`, no uniform upper bound for `M`, and no link-cardinality-independent certificate has been shown.

**Previous CL obstruction was already closed qualitatively by CO #5440** before DV. The novelty of DV is a positive *quantitative* all-`L²` coefficient, not the first proof of `ker(AW)=V`.

### 2.3 Distinct full physical twelve-color Dirichlet chain

```text
BC/CA/BZ    E12 physical normalized 12-color energy, true positive self-adjoint D12;
DR          bounded original Wilson physical variance <= (1/kappa) * E12;
DS          all x:HW, kappa * ||x-Pconst(x)||² <= E12(x);
DT          kappa • (identity - Pconst) <= D12   (genuine Loewner order);
DU          D12 kills Wilson constant-line and preserves its orthogonal;
            restricted D12 self-adjoint on Vᗮ;
            spectrum_R(D12|Vᗮ) subset [kappa, +infinity).
```

In DU, the spectrum result follows from **resolvent invertibility** via pinned mathlib, *not* by assuming an eigenbasis of an infinite-dimensional operator.

**Keep the order of logic:** original normalized Haar reference ≤ E12 was established earlier; it alone does **not** imply the original Haar reference has a positive lower bound. DQ + DF + DV supply the independent missing direction.

## 3. Closed DW–DZ: original Riesz operator, explicit physical coefficient, exact 12-fold unnormalization; H-uniformity OPEN

**P4-Q2-DW [PR #5475] — CLOSED.** On the genuine original Wilson joint physical Hilbert `HW`, DW proves

```text
exists kappa_R>0, kappa_R • (identity-Pconst) <= AW
ker(AW)=V  (already closed qualitatively by CO)
AW(V)=0,  AW(HW) subset Vᗮ
AW|Vᗮ is a continuous self-adjoint real-linear endomorphism
spectrum_R(AW|Vᗮ) subset [kappa_R, +infinity)
exists kappa_R>0, kappa_R • D12 <= AW <= 12 • D12
```

The reverse comparison is now a **proved** mathlib `ContinuousLinearMap` Loewner theorem. It did not follow from CA's older upper inequality alone.

**P4-Q2-DX [PR #5476] — CLOSED.** Uses BY's actual original UNNORMALIZED Haar sum quadratic upper coefficient `12`, DW's actual positive restricted Rayleigh estimate, and pinned mathlib's `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map`:

```text
IsUnit (AW|Vᗮ)  -- a genuine bounded operator inverse exists at each finite H
exists kappa_R>0, spectrum_R(AW|Vᗮ) subset [kappa_R, 12]
0 notin spectrum_R(AW|Vᗮ).
```

**P4-Q2-DY [PR #5478] — CLOSED:** the coefficient's exact DQ/DF dependence is now a **Lean definition plus existential genuine Wilson mass/variance witnesses**, not merely a README formula. `p4Q2DY_originalFullJointRieszQuadratic_explicitCoefficient` establishes positive `kappa_exp=min(1,m exp(-32beta)/(12 spatialLinkCard(H) (M+1)))` on the **actual full physical joint L²**. `p4Q2DY_originalRestrictedRiesz_explicitAntilipschitz` transfers the SAME coefficient to the original Riesz orthogonal-restriction stability. Uses original-normalized Haar → unnormalized literal Haar → full Hilbert L², without Wilson/pair-Haar mean or D12 substitution.

**P4-Q2-DZ [PR #5480] — CLOSED.** This is the exact original Wilson Haar 12-color normalization bridge: DQ/DY lower-bound the ORIGINAL normalized average; the literal BY/BX physical Haar Riesz quadratic is the UNNORMALIZED sum. In the pinned Lean ENNReal type, DZ multiplies by twelve and proves exact cancellation with the `(12:ENNReal)⁻¹` in BC, instead of DY's lossy normalized ≤ unnormalized bound. Hence the SAME genuine mass/variance witnesses m,M satisfy

```text
kappa_DZ(H,beta,m,M) = 12 * kappa_DY(H,beta,m,M) > kappa_DY(H,beta,m,M) > 0
kappa_DY = min(1, m*exp(-32*beta) / (12*spatialLinkCard(H)*(M+1))).
```

The explicit normalized-to-original-sum inequality, full physical joint L² quadratic, original Riesz Loewner bound, and restricted anti-Lipschitz estimate all use this same improved coefficient. It is a real proof-certificate gain, NOT the removal of the inherent finite-size averaging factor or a new physical Hamiltonian.

**Next OPEN P4-Q2-EA / uniformity research:** test and prove genuine original physical block/colored refresh or covariance cancellation controlling the remaining `1/spatialLinkCard(H)` and the H-dependent Wilson mass floor `m`, variance comparison `M`. A bare rescaling by spatial link count is not a Wilson time-transfer spectral gap or continuum OS Hamiltonian. A positive H-independent bound remains unproved; signed physical fine/frozen Krylov and C1/C2/C3/H2/H3/H4 remain OPEN.

**Still OPEN:** physical signed fine/frozen Krylov Gram uniformity; C1 common-marginal physicality, C2 vector-wise reconstruction, C3 summable genuine beta trajectory; H2 spacing-scaled nontrivial evolution, H3 OS Hamiltonian, H4 4D Yang–Mills continuum existence and positive mass gap.

## 4. Independent live frontier: signed uncentered physical fine/frozen Krylov Gram

P4-Q2-DV does **not** supply the unresolved uniform signed physical Krylov Gram bound. Keep the older line active where it remains physically relevant.

Original objects at finite H:

```text
R_(n,j)  = original uncentered fine-right Krylov orbit at beta_(n+1);
V_frozen = actual physical frozen receiver at beta_n;
Q_(beta_n,e) = U_(beta_n)^(-1) P_(beta_n,e) U_(beta_n);
r_(e,j)  = (id-Q_(beta_n,e)) V_frozen(R_(n,j));
G_ij     = sum_e inner(r_(e,i),r_(e,j));
F_a      = sum_j a_j R_(n,j).
```

The original signed Rayleigh equals **half the actual original two-copy resampling energy** (#5324), not an artificial independent product energy. #5321's `ℓ²` Schur theorem is **conditional** on a signed row majorant.

The strongest constructed linkwise estimate of #5326 is:

```text
V_joint(F_a) = W_(beta_n) * M_(beta_n,F_a)
b_e(F_a) = ||W|| * osc_e(M_(F_a)) + ||M_(F_a)|| * osc_e(W)
a* G_right a <= (1/2) * sum_e b_e(F_a)^2 .
```

**Work remaining:**
- Control `osc_e(W)` from the ACTUAL Wilson joint density, positive continuous vacuum and square-root half-density normalization. The local raw-action oscillation `8`, `exp(8 beta)` Harnack factor and positive kernel bounds do not alone bound the complete `W`.
- Control `osc_e(M_(F_a))` with genuinely **signed** fine/frozen physical inputs; never substitute a positivity assertion for signed integrals or discard output drift.
- Prove physical spatial tail/summability or cancellation yielding an H-independent `sum_e b_e(F_a)^2 ≤ C * sum_j a_j²`, or prove the original signed covariance row bound needed by #5321. A coefficient-`ℓ¹` or `|E_H|` estimate is not `ℓ²` operator closure.
- Check rank, spatial horizon and distinct `beta_n`/`beta_(n+1)` compatibility. Neither a fixed-H AW nor D12 gap proves a common bound across `n`.

**Acceptance:** actual original-law posterior/receiver, all signed mode covariances, exact fine/frozen scales and a constant justified independent of spatial volume where uniformity is asserted.

## 5. Spatial-volume / lattice-spacing frontier: distinguish three kinds of gaps

| Statement | Formal status | What extra proof is needed |
| --- | --- | --- |
| Positive `κ_R(H,N,beta)` and bounded inverse for original AW on `Vᗮ` | **PROVED (DV/DW/DX/DY/DZ)** finite H; DX spectral band `[κ_R,12]`, DY genuine typed m,M, DZ exact improved coefficient `12*κ_DY` with Loewner and anti-Lipschitz. | H-/spacing-uniform κ still OPEN; must control link averaging, original m,M, or replace the comparison. |
| Positive `κ_12(H,N,beta)` for physical D12 on `Vᗮ` | **PROVED (DU)**. | Prove a suitable H/spacing-scale statement for the actual dynamics; do not identify `D12` with AW or physical transfer generator. |
| Genuine Wilson 4D continuum mass gap | **OPEN**. | Physical common marginals and reconstruction, spacing-scaled semigroup/generator, OS Hamiltonian, positive Wightman/Yang–Mills continuum spectrum. |

**Finite-volume constants cannot simply be renamed “uniform.”** Some earlier restricted-beta twelve-color physical frame results have `κ_12 ≥ 1/2304`, transfer gap `≥ 1/3072`, `q0=3071/3072` in their **specific** proven contexts. Applying a fixed contraction to `floor(t/a_n)` as `a_n→0` may produce a degenerate semigroup, not a nontrivial time-evolution. An actual spacing-scaled generator and suitable rate must be proved.

For the new DV certificate, the explicit factor `1/spatialLinkCard(H)` and volume-dependent genuine density floor `m(H,N,beta)` are visible obstructions to naively claiming uniformity. Seek better physical locality/sum estimates or a different rigorously justified coercivity route; do not postulate an H-independent mass floor.

## 6. Adjacent-scale / continuum requirements (unchanged and OPEN)

| Gate | Precise acceptance condition |
| --- | --- |
| **C1 — physicality / leakage** | Coarse candidates live in the actual coarse **physical Hilbert space** with a compatible common marginal; posterior averaging alone does not establish physicality. |
| **C2 — vector-wise reconstruction/transfer** | Prove actual fine evolution and reconstruction versus coarse physical transfer errors on the relevant `r,k` inputs, in a norm strong enough to pass to a common operator, with controlled scale sum. |
| **C3 — weighted beta trajectory** | Construct an explicit genuine path `beta_n` with sufficiently summable physically proved response/transfer coefficients weighted by `|beta_(n+1)-beta_n|`. |
| **Common natural-time compatibility** | Show iterates at different times are powers of **one** limiting physical operator (not unrelated pointwise limits). |
| **H2 — nontrivial physical time** | Prove the spacing-scaled strongly continuous semigroup/generator, not only a finite-spacing contraction. |
| **H3 — OS Hamiltonian** | Actual continuum reflection-positive/OS physical reconstruction, self-adjoint positive generator, vacuum sector and appropriate localization. |
| **H4 — continuum mass gap** | Prove the Wightman/Yang–Mills existence and spectrum axioms for the reconstructed continuum theory with a nonzero physical energy–momentum mass gap. |

**All C1/C2/C3/H2/H3/H4 obligations remain OPEN**, irrespective of the positive finite-volume AW and D12 spectral certificates.

## 7. Historical supporting lanes and no-go safeguards

P3 posterior-locality/seed machinery (#5208–#5235) is supporting infrastructure, **not** the default active Dobrushin reconstruction loop. It contains real six-color and twelve-resampling identities, local seed distances, true original posterior source-only tilts and covariance estimates under their own hypotheses. The signed physical receiver bridge and global original frozen-link sum were not thereby established uniformly.

Proved limited obstructions must not be enlarged into universal impossibility:
- Positive-SU(2)-coupling old H1-D5 whole-operator compatibility is a no-go for that specified route.
- #5207 rules out a particular fixed-`s>8` strict Dobrushin finite-positive-mass scaling certificate; it is **not** a no-go for all continuum methods.
- #5217's uncorrected sup-width majorants cannot furnish the sought estimate; newer true signed-`L²` and Haar mass-floor routes are different.

Other hard boundaries: no equality of Wilson and pair-Haar means, no unsupported commutation of interacting conditional projections, no pointwise substitution for a.e. equalities, no finite-support assumption for positive-depth Krylov or the nonlocal vacuum, no `abs(x)` transfer contraction without excited-sector preservation, and no inverse inequality inferred from a one-direction Loewner comparison.

## 8. Exact source chain / reproducibility

All sources below are under `MGAP4D/MathlibAnalytic/` and share the `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar` prefix unless stated otherwise.

| Step | Exact suffix (append `.lean`) | PR |
| --- | --- | --- |
| Original physical Riesz quadratic | `OriginalFullJointL2Quadratic` / `OriginalFullJointL2RieszOperator` | #5422 / #5423 |
| Qualitative all-`L²` kernel CLOSED | `OriginalFullL2QualitativeKernelCollapse` | #5440 |
| Independent Haar global-mean Poincaré | `GlobalMeanPoincare` | #5455 |
| Wilson / pair-Haar variance | `OriginalPhysicalVarianceSandwich` | #5457 |
| Original twelve-color Haar mass floor | `OriginalTwelveColorPositiveHaarFloor` | #5458 |
| Original Haar versus coordinate L² defect | `OriginalTwelveColorHilbertResidualLowerBound` | #5467 |
| Actual normalized color→all links | `OriginalTwelveColorGlobalHilbertFloor` | #5468 |
| Genuine bounded Wilson variance bound | `OriginalWilsonVarianceTwelveColorCoercivity` | #5469 |
| Full physical D12 coercivity | `OriginalWilsonFullJointL2PhysicalFrameCoercivity` | #5470 |
| Physical operator Loewner | `OriginalPhysicalTwelveDirichletOperatorGap` | #5471 |
| Restricted D12 real spectrum | `OriginalPhysicalTwelveDirichletOrthogonalSpectrum` | #5472 |
| **Original Wilson Haar Riesz full-`L²` coercivity** | **`OriginalFullJointHaarRieszCoercivity`** | **#5473** |
| Original AW Loewner / restricted floor / D12 bilateral | `OriginalWilsonRieszOrthogonalSpectrum` | #5475 |
| **Original AW restricted IsUnit and spectral band** | **`OriginalWilsonRieszSpectralBandAndIsUnit`** | **#5476** |
| **Explicit genuine original Wilson DQ/DF coefficient to full L² and anti-Lipschitz** | **`OriginalWilsonRieszExplicitFiniteVolumeCertificate`** | **#5478** |
| **Exact original unnormalized 12-color coefficient and improved same-witness full-L²** | **`OriginalWilsonRieszExactUnnormalizedTwelveFactor`** | **#5480** |

Minimal latest Lean target after checking out the newly observed authoritative branch:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExactUnnormalizedTwelveFactor
```

**Proof-integrity process:** exact authoritative branch SHA first; exact Lean file, dependencies and physical definitions second; docs and exact-source-head CI after that. Inspect the full error context and pinned mathlib syntax, not just the highlighted line. No new `sorry`, `admit`, `axiom` or hidden synthetic physical laws. Preserve true original sum/average normalization, and explicitly report nonfatal warnings (DV had four). Use targeted changed-Lean CI and reusable pinned caches where possible; do not rebuild the entire project needlessly. For a documentation-only update, modify **only README.md and ROADMAP.md** and do not present its resulting merge SHA as a new theorem-bearing checkpoint.
