# MGAP4D — four-dimensional Yang–Mills formalization

Lean 4 / mathlib research by **Hidetoshi Itakura** on the original finite-volume Wilson lattice theory and the outstanding four-dimensional Yang–Mills existence and mass-gap problem.

**Checkpoint — 2026-10-12 JST:** latest theorem-bearing [PR #5480 (P4-Q2-DZ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5480) is **MERGED** at `d4674e05b4ce1a21ffcdffce42b7de4f5a55df7c`; exact-source-head [CI #38230569714](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38230569714) **SUCCESS (9533/9533)**. DY #5478 and preceding physical Riesz operator proofs also remain merged.

> **Scope.** Original Wilson Haar Riesz `AW`: actual full-physical-joint-`L²` finite-volume quadratic coercivity (DV), genuine Loewner/restriction (DW), bounded inverse and real spectral band `[κ_R,12]` (DX). **DY #5478 Lean-proves the original physical DQ/DF finite-volume witness coefficient; DZ #5480 restores the EXACT factor 12 lost when going from the original normalized Haar average to its truly UNNORMALIZED twelve-color sum, improving the SAME physical coefficient across full-L², Loewner and anti-Lipschitz bounds**. Separate normalized physical `D12` and independent pair-Haar coordinate projections are never identified. **No spatial-volume/spacing-uniform coefficient, Yang–Mills continuum theory or positive continuum mass gap is claimed.**

See the updated [ROADMAP.md](ROADMAP.md) for the theorem-status matrix, independent Krylov/adjacent-scale obligations, and the next proof order.

## 1. Authority and reproducible environment

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Latest theorem-bearing merge** | [#5480 (DZ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5480), `d4674e05b4ce1a21ffcdffce42b7de4f5a55df7c` |
| PR #5480 exact tested source HEAD | `b057e2e618de7597478b909a85807839ed824ff8` |
| Lean pin | `leanprover/lean4:v4.30.0-rc2` |
| mathlib pin | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact source-head CI | [#38230569714](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38230569714) — **SUCCESS** |
| Changed Lean / MCP completion jobs | `114748729543` / `114750270625`, both **SUCCESS** |
| Build and diagnostics | **9533/9533**, **0 DZ changed-file errors/warnings**; preflight audit passed. `#print axioms` shows standard Lean axioms and inherited original `native_decide` dependencies (spatial color, incident plaquettes, other-axis cardinality). No new axiom declaration, no `sorryAx` in final successful proof. Historical DV had four nonfatal warnings. |

**The GitHub default `main` is not the theorem authority.** Reobserve the fresh exact HEAD of the branch above and inspect the actual Lean theorem declarations before trusting this document, a PR title, or a historical conversation. A subsequent documentation-only merge advances the branch HEAD **without changing the #5480 theorem-bearing checkpoint**.

Authority order: fresh authoritative SHA → actual Lean statements/proofs → README/ROADMAP → CI for that exact SHA → historical reports.

## 2. Three distinct mathematical objects — never interchange them

Fix a genuine finite Wilson configuration satisfying the Lean hypotheses (in particular `0 < N` and `0 ≤ beta`), and write:

- `muW`: actual original Wilson physical ground-state **joint** probability law; `HW`: its real joint `Lp ℝ 2 muW`.
- `muPair`: actual independent **pair-Haar** law on the matching joint configuration carrier; the two expectations and associated conditional projections are *not identified*.
- `V`: the physical Wilson constant line, and `Pconst`: its Hilbert orthogonal projection.

**Original Haar-reference Riesz quadratic:** `QW(f) = p4Q2BX_originalFullJointQuadratic ... f`, the unique continuous quadratic extension (BW/BX) of the literal original Wilson mass-weighted **unnormalized 12-color Haar reference sum** on bounded observables. BY constructs its positive self-adjoint Riesz operator `AW` with `QW(f) = inner ℝ (AW f) f`.

**Physical twelve-color Dirichlet energy:** `E12(f)`, the separate **normalized** (factor `1/12`) sum of squared residuals of the actual original Wilson physical conditional-expectation projections. CA builds `D12` as the genuine 12-color residual Gram operator, with `inner ℝ (D12 f) f = E12(f)`.

**Pair-Haar coordinate defects:** `sum_i ‖f - P_i f‖²` uses *independent pair-Haar* coordinate `CondExpL2` projections. Their proved commutation is **not** a positive-beta commutation assertion for physical Wilson conditional expectations.

The normalizations matter: the DQ/DR **normalized reference** is `(1/12) * (original 12-color sum)`, whereas `QW` extends the **sum**. Keep source/frozen `beta_n` distinct from fine `beta_(n+1)` when discussing adjacent-scale Krylov inputs.

## 3. Original Wilson Riesz: DV quadratic → DW/DX operator → DY explicit and DZ exact-12 coefficients

[PR #5473](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5473) adds `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointHaarRieszCoercivity.lean`. Its final Lean theorem is:

```lean
theorem p4Q2DV_originalWilsonFullJointRieszQuadratic_coercive :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ x : J, κ * ‖x - B x‖ ^ 2 ≤ Q x
```

Here `J`, `B`, and `Q` denote **the actual original Wilson** joint `L²`, physical constant projection, and original Haar-reference quadratic in that file.

The verified proof sequence is:

1. **DQ + genuine pair-Haar DC + genuine Wilson/pair-Haar DF:** lower-bound the original **normalized Wilson Haar reference** by a positive finite-volume coefficient times **actual Wilson variance** on every bounded strongly measurable physical observable. This extracts the intermediate bound already present in DR, before DR's separate `E12` upper comparison.
2. **Literal normalization:** compare `(1/12) * sumRef ≤ sumRef`, use the proved finite original Haar sum, and convert to real scalars with positive finite `min κ 1`; no extra measure or unjustified equality of means.
3. **Actual bounded Wilson core and quotient:** BR/CL identify its true physical `L²` representative; DS proves centered squared Hilbert norm ≤ true Wilson variance.
4. **Density + continuity:** BW's genuine dense bounded-core image and BX's continuous `QW` extend **the same finite-volume coefficient** to every physical joint `L²) class.

This is quantitatively stronger than the **already established** full-`L²` qualitative kernel identity `ker(AW) = V` from **P4-Q2-CO, PR #5440**. DV did **not** first prove qualitative kernel closure; it supplies a positive quadratic coefficient. Do not revive CL's historical kernel obstruction as if CO had not closed it.

**Operator/spectrum corollaries are now Lean-proved.** [#5475 (DW)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5475) proves actual original-`AW` Loewner coercivity `κ_R • (id-Pconst) ≤ AW`, its zero action on physical constants, self-adjoint bounded restriction to `Vᗮ`, its positive real spectral half-line, and the genuine finite-volume bilateral comparison `κ_R • D12 ≤ AW ≤ 12 • D12` (BF supplies the independent upper `E12 ≤ ‖x-Pconst x‖²` input). These comparisons do **not** identify `AW` with `D12`.

**[#5476 (DX)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5476) upgrades the ACTUAL original Wilson Riesz orthogonal restriction `AW|Vᗮ`:**

- `p4Q2DX_restrictedOriginalWilsonRiesz_isUnit`: `AW|Vᗮ` is a unit in the actual bounded-real-linear-operator Banach algebra, hence has a bounded inverse at each fixed volume.
- `p4Q2DX_restrictedOriginalWilsonRiesz_spectrum_subset_Icc`: `∃ κ_R>0, spectrum ℝ (AW|Vᗮ) ⊆ Set.Icc κ_R 12`. The upper edge `12` comes from BY's original **unnormalized** Haar-reference quadratic, not the normalized physical `D12`.
- `p4Q2DX_restrictedOriginalWilsonRiesz_zero_notMem_spectrum`: zero is excluded from the REAL restricted spectrum; resolvent invertibility uses pinned mathlib, with no eigenbasis or compactness assumption.

**DY #5478: explicit ORIGINAL physical finite-volume certificate, now Lean-proved (not merely an explanatory formula).** The new definition `p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M` retains exactly

```text
a(H,beta,m) = p4Q2DQ_allLinkHilbertFloorCoefficient H beta m
            = m * exp(-32*beta) / (12 * spatialLinkCard(H))   -- explanatory real form
kappa_exp(H,beta,m,M)
  = (min (a(H,beta,m) * (ENNReal.ofReal (M+1))^(-1)) 1).toReal
```

in its **actual ENNReal-typed Lean definition**. DY proves `∃ m M, 0 < m ∧ 0 ≤ M ∧ 0 < kappa_exp ∧ ∀ x : genuine Wilson physical joint L², kappa_exp * ‖x-Pconst x‖² ≤ Q_original(x)`, using actual DQ/DF witnesses. It then proves quantitative `AntilipschitzWith (c⁻¹) (AW|Vᗮ)` with `(c:ℝ)=kappa_exp`: the explicit coefficient controls the stability of the actual restricted inverse. The exact true original Wilson/Haar normalizations and BW/BX density are retained. **This certificate still has the factor `1/spatialLinkCard(H)` and H-dependent `m,M`; uniformity is OPEN.**

**DZ #5480: EXACT unnormalized Wilson Haar reference sum (new Lean theorem).** DY used the safe but lossy inequality `normalized 12-color average ≤ unnormalized 12-color sum`. DZ uses the literal original normalized definition to prove equality after multiplying by twelve in `ENNReal`. For the **same** genuine original DQ mass `m>0` and DF variance comparison `M≥0`, the typed coefficient is

```text
kappa_DZ(H,beta,m,M) = 12 * p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M
                    = 12 * min(1, m*exp(-32*beta)/(12*spatialLinkCard(H)*(M+1)))
                    > p4Q2DY_originalRieszFiniteVolumeCoefficient H beta m M > 0.
```

The displayed real quotient is an explanatory normalization of the actual `ENNReal`-based Lean definition. `p4Q2DZ_originalWilsonUnnormalizedReference_exactTwelveWitness` proves the improved bounded original-Wilson reference/variance inequality; `p4Q2DZ_originalFullJointRieszQuadratic_exactTwelveCoefficient` extends the **identical improved coefficient** to all actual physical joint `L²` classes. `p4Q2DZ_originalWilsonRiesz_exactTwelveLoewner` establishes the genuine original Riesz operator centered projection order, and `p4Q2DZ_originalRestrictedRiesz_exactTwelveAntilipschitz` sharpens the actual restricted inverse stability. This improves the old *certificate*, not the underlying physical operator or its volume-uniformity. **The inverse spatial-link-cardinality and the H-dependent m,M remain.**


## 4. Separately established physical D12 gap (DS–DU)

The independent physical Dirichlet route is already formalized:

| PR | Verified formal result |
| --- | --- |
| [#5469 (DR)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5469) | Genuine finite-volume Wilson probability-variance lower bound by physical E12 for all bounded strongly measurable observables. |
| [#5470 (DS)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5470) | One positive coefficient for **all** original physical joint `L²` classes: `κ ‖x-Pconst x‖² ≤ E12(x)`. |
| [#5471 (DT)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5471) | Genuine `ContinuousLinearMap` Loewner bound `κ • (I-Pconst) ≤ D12`; positive Rayleigh bound on `Vᗮ`. |
| [#5472 (DU)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472) | `D12` kills `V`, preserves `Vᗮ`, and its **actual restricted self-adjoint operator** has `spectrum ℝ (D12|Vᗮ) ⊆ Set.Ici κ` for some `κ>0`. |

CA/BZ prove `0 ≤ AW ≤ 12 • D12`; **DW #5475 additionally proves the reverse finite-volume operator inequality** `κ_R • D12 ≤ AW`. This is a genuine operator comparison of **distinct** `ContinuousLinearMap` endomorphisms, not an identification or an H-uniform bound.

The DU spectrum theorem applies to the **physical normalized D12**; DW and DX independently prove the restricted spectral statements for the **original unnormalized Wilson Haar AW**. Neither proves uniformity as H grows or the lattice spacing tends to zero.

## 5. Earlier finite-volume gates and original physical chain

| Lane | Formal status and principal PRs | Still required |
| --- | --- | --- |
| **P4-F1/F2/F3** | **CLOSED** (#5299–#5302): original fourfold a.e. lift, genuine retained-sigma descent, strict positive-`beta` original Wilson vacuum-fiber energy at each finite H. | No implication of an H-uniform lower rate. |
| **P4-Q1** | Quantitative at fixed H (#5303–#5309): `0 < E_vac(beta,H) ≤ |SpatialLinks(H)| (exp(16 beta)-1)^2` in its stated range. | Remove/control the spatial-cardinality factor. |
| **P4-Q2, signed physical Krylov Gram** | #5310–#5326: uncentered physical receiver, original signed covariance, exact two-copy resampling, constructed `W × M` BCF per-link oscillation budget. | Spatially summable **H-uniform** signed/operator-`ℓ²` control is OPEN. |
| **P4-Q2, original reference construction** | #5389–#5427: original bounded-core polarization, full joint L² Riesz AW, positivity and earlier one-sided comparison. | Extended in DW/DX; volume-uniform physicality OPEN. |
| **P4-Q2, zero/kernel and pair-Haar bridges** | #5431–#5440 **CO** qualitative full-`L²` kernel, #5441 mass floor, #5442–#5455 actual pair-Haar coordinate tensorization/Poincaré, #5456–#5467 Wilson variance/fiber bridges. | Preserve actual conditional laws; no synthetic independence. |
| **P4-Q2, quantitative full-`L²`** | **#5468–#5480 CLOSED**: DQ/DR → DS–DU physical D12 → DV original AW quadratic → DW Loewner/D12 comparison → DX restricted spectral band → DY explicit DQ/DF coefficient → **DZ exact unnormalized 12-color factor, improved whole L², Loewner and inverse stability**. | Physical H-/spacing-uniformity, signed Gram and adjacent-scale/continuum reconstruction remain OPEN. |

The #5326 `W × M` signed-Krylov link-budget and the newer AW/D12 finite-volume spectral gap are **different mathematical problems**. A finite-volume positive coefficient for AW or D12 does not close the volume-uniform fine/frozen Krylov Gram, original signed Schur row estimates, or cross-scale reconstruction.

## 6. Live frontier and limitations

With finite-volume AW operator/spectrum consequences CLOSED through DX, typed DQ/DF witness propagation CLOSED by DY, and exact original twelve-color coefficient recovery CLOSED by DZ, the active mathematical tasks are (i) replace or control DQ's explicit inverse spatial-link-cardinality loss and true Wilson fiber-mass/variance comparison dependence **without postulating an H-independent floor**, (ii) physically justified **uniform-in-H and spacing-scaled** signed Krylov/adjacent-scale Gram estimates, (iii) C1 actual common-marginal physicality, C2 fine/coarse vector reconstruction, C3 an explicit summable genuine beta trajectory, and (iv) H2 physical time generator/strongly continuous semigroup, H3 OS Hamiltonian, H4 positive **continuum** Yang–Mills mass gap. All continuum gates remain **OPEN**.

Do not treat positive constants separately available at each H as a common constant. The DV proof uses a finite-volume coefficient from an actual Wilson Haar fiber-mass floor and link cardinality; no bound uniform in H is proved. Existing small-beta estimates `κ12 ≥ 1/2304`, transfer gap `≥ 1/3072`, `q0=3071/3072` apply only within their verified contexts; they are **not** a nontrivial continuum time evolution.

Prior no-go/limits remain relevant: positive-coupling H1-D5 whole-operator compatibility; the specific fixed-`s>8` Dobrushin scaling certificate (#5207); and old uncorrected sup-width majorants (#5217). They do **not** refute all continuum routes. Avoid reconstructing the failed Dobrushin architecture as the default path.

## 7. Reading and reproducing the current theorem

The latest theorem-bearing Lean target lives at:

```text
MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExactUnnormalizedTwelveFactor.lean
```

On the **fresh authoritative branch** with the pinned toolchain/manifest:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonRieszExactUnnormalizedTwelveFactor
```

Read in dependency order: DQ `OriginalTwelveColorGlobalHilbertFloor` → DC `GlobalMeanPoincare` → DF `OriginalPhysicalVarianceSandwich` → DR `OriginalWilsonVarianceTwelveColorCoercivity` → CL `OriginalBoundedCoreKernelExactFrontier` → BW/BX `OriginalFullJointL2ContinuousBilinear` / `OriginalFullJointL2Quadratic` → **DV** `OriginalFullJointHaarRieszCoercivity` → **DW** `OriginalWilsonRieszOrthogonalSpectrum` → **DX** `OriginalWilsonRieszSpectralBandAndIsUnit` → **DY** `OriginalWilsonRieszExplicitFiniteVolumeCertificate` → **DZ** `OriginalWilsonRieszExactUnnormalizedTwelveFactor`. All these shorthand names share the full `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar` prefix and `MGAP4D/MathlibAnalytic/` directory.

For the physical D12 spectrum, follow CA `OriginalPhysicalTwelveDirichletLoewner` → DS `OriginalWilsonFullJointL2PhysicalFrameCoercivity` → DT `OriginalPhysicalTwelveDirichletOperatorGap` → DU `OriginalPhysicalTwelveDirichletOrthogonalSpectrum`.

**Audit policy:** On theorem PRs verify original physical meanings, all changed Lean files **and their dependencies**, frozen Lean/mathlib pins, exact tested PR HEAD, success of targeted Lean CI plus its matching MCP receipt, and absence of new `sorry`/`admit`/axioms. Do not report warnings as zero when CI shows otherwise. On a **documentation-only** PR, change only README/ROADMAP; it moves branch HEAD but does not constitute a new mathematical theorem.
