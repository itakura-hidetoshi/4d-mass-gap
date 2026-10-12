# MGAP4D — four-dimensional Yang–Mills formalization

Lean 4 / mathlib research by **Hidetoshi Itakura** on the original finite-volume Wilson lattice theory and the outstanding four-dimensional Yang–Mills existence and mass-gap problem.

**Checkpoint — 2026-10-12 JST:** theorem-bearing [PR #5473](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5473) (P4-Q2-DV) is **merged**, at commit `5c19cab77627673818c10926be876c009245feb8`. Its exact-source-head Lean CI is [#38218052792](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38218052792), **SUCCESS**.

> **Scope.** The original Wilson Haar-reference Riesz quadratic now has a strictly positive **finite-volume** coercivity coefficient on the **entire actual physical joint real (L^2)**, modulo genuine Wilson constants. The separate physical 12-color Dirichlet operator also has a verified positive finite-volume orthogonal-sector spectral floor. **Neither result establishes an estimate uniform in spatial volume or lattice spacing, a continuum quantum Yang–Mills theory, or a positive continuum mass gap.**

See the updated [ROADMAP.md](ROADMAP.md) for the theorem-status matrix, independent Krylov/adjacent-scale obligations, and the next proof order.

## 1. Authority and reproducible environment

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Latest theorem-bearing merge** | [#5473](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5473), `5c19cab77627673818c10926be876c009245feb8` |
| PR #5473 exact tested source HEAD | `d9b1306c69d22e98d69f1830d9e803db0b518d3a` |
| Lean pin | `leanprover/lean4:v4.30.0-rc2` |
| mathlib pin | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact source-head CI | [#38218052792](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38218052792) — **SUCCESS** |
| Changed Lean / MCP completion jobs | `114707347025` / `114708636678`, both **SUCCESS** |
| Build and diagnostics | **9528/9528** jobs, **0 errors; 4 non-fatal unused-variable warnings** in new DV Lean file; forbidden-token audit passed |

**The GitHub default `main` is not the theorem authority.** Reobserve the fresh exact HEAD of the branch above and inspect the actual Lean theorem declarations before trusting this document, a PR title, or a historical conversation. A subsequent documentation-only merge will advance the branch HEAD **without changing the #5473 theorem-bearing checkpoint**.

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

## 3. Latest result — quantitative full-physical-L² original Wilson Riesz coercivity (DV)

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

**Not yet separately packaged as Lean operator/spectrum corollaries for AW:** `κ • (I - Pconst) ≤ AW`, its orthogonal-restriction positive real spectrum floor, and the ensuing quantitative comparison with D12. These are next proof tasks, not statements already present in DV.

## 4. Separately established physical D12 gap (DS–DU)

The independent physical Dirichlet route is already formalized:

| PR | Verified formal result |
| --- | --- |
| [#5469 (DR)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5469) | Genuine finite-volume Wilson probability-variance lower bound by physical E12 for all bounded strongly measurable observables. |
| [#5470 (DS)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5470) | One positive coefficient for **all** original physical joint `L²` classes: `κ ‖x-Pconst x‖² ≤ E12(x)`. |
| [#5471 (DT)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5471) | Genuine `ContinuousLinearMap` Loewner bound `κ • (I-Pconst) ≤ D12`; positive Rayleigh bound on `Vᗮ`. |
| [#5472 (DU)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472) | `D12` kills `V`, preserves `Vᗮ`, and its **actual restricted self-adjoint operator** has `spectrum ℝ (D12|Vᗮ) ⊆ Set.Ici κ` for some `κ>0`. |

CA/BZ also prove the **one-sided** original reference/physical comparison `0 ≤ AW ≤ 12 • D12`, in the actual physical Hilbert operator order. **No reverse comparison of AW and D12 should be marked Lean-complete until a theorem proves it in the appropriate operator type** (DV may supply the mathematical input, but is a quadratic theorem).

The DU spectral statement is for the **physical D12 restricted to actual Wilson constants' orthogonal complement**, *not* for AW. Neither DU nor DV establishes a uniform gap as lattice spacing tends to zero.

## 5. Earlier finite-volume gates and original physical chain

| Lane | Formal status and principal PRs | Still required |
| --- | --- | --- |
| **P4-F1/F2/F3** | **CLOSED** (#5299–#5302): original fourfold a.e. lift, genuine retained-sigma descent, strict positive-`beta` original Wilson vacuum-fiber energy at each finite H. | No implication of an H-uniform lower rate. |
| **P4-Q1** | Quantitative at fixed H (#5303–#5309): `0 < E_vac(beta,H) ≤ |SpatialLinks(H)| (exp(16 beta)-1)^2` in its stated range. | Remove/control the spatial-cardinality factor. |
| **P4-Q2, signed physical Krylov Gram** | #5310–#5326: uncentered physical receiver, original signed covariance, exact two-copy resampling, constructed `W × M` BCF per-link oscillation budget. | Spatially summable **H-uniform** signed/operator-`ℓ²` control is OPEN. |
| **P4-Q2, original reference construction** | #5389–#5427: real Wilson joint Dirichlet, bounded-core polarization, uniquely extended bilinear/positive quadratic, original positive self-adjoint Riesz AW, one-sided Loewner comparison. | See next AW operator corollaries and uniformity. |
| **P4-Q2, zero/kernel and pair-Haar bridges** | #5431–#5440 **CO** qualitative full-`L²` kernel, #5441 mass floor, #5442–#5455 actual pair-Haar coordinate tensorization/Poincaré, #5456–#5467 Wilson variance/fiber bridges. | Preserve actual conditional laws; no synthetic independence. |
| **P4-Q2, quantitative full-`L²`** | **#5468–#5473 CLOSED**: DQ reference lower bound → DR variance → DS D12 Hilbert coercivity → DT/DU D12 operator/spectrum → **DV original AW quadratic coercivity**. | AW operator/spectrum corollaries; then truly **uniform** finite-volume/scale bounds. |

The #5326 `W × M` signed-Krylov link-budget and the newer AW/D12 finite-volume spectral gap are **different mathematical problems**. A finite-volume positive coefficient for AW or D12 does not close the volume-uniform fine/frozen Krylov Gram, original signed Schur row estimates, or cross-scale reconstruction.

## 6. Live frontier and limitations

The next tasks are: (i) formal AW operator Loewner/coercivity and restricted-spectrum corollaries from DV (with CO), (ii) quantitative **uniform-in-H and spacing-scaled** bounds for the actual physical family, including the signed uncentered Krylov/adjacent-scale Gram, (iii) C1 actual common-marginal physicality, C2 vector-wise coarse/fine reconstruction compatibility, C3 a summable explicit beta trajectory, and (iv) H2 physical time generator/strongly continuous semigroup, H3 OS Hamiltonian, H4 positive **continuum** Yang–Mills mass gap. All continuum gates remain **OPEN**.

Do not treat positive constants separately available at each H as a common constant. The DV proof uses a finite-volume coefficient from an actual Wilson Haar fiber-mass floor and link cardinality; no bound uniform in H is proved. Existing small-beta estimates `κ12 ≥ 1/2304`, transfer gap `≥ 1/3072`, `q0=3071/3072` apply only within their verified contexts; they are **not** a nontrivial continuum time evolution.

Prior no-go/limits remain relevant: positive-coupling H1-D5 whole-operator compatibility; the specific fixed-`s>8` Dobrushin scaling certificate (#5207); and old uncorrected sup-width majorants (#5217). They do **not** refute all continuum routes. Avoid reconstructing the failed Dobrushin architecture as the default path.

## 7. Reading and reproducing the current theorem

The latest Lean target lives at:

```text
MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointHaarRieszCoercivity.lean
```

On the **fresh authoritative branch** with the pinned toolchain/manifest:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFullJointHaarRieszCoercivity
```

Read in dependency order: DQ `OriginalTwelveColorGlobalHilbertFloor` → DC `GlobalMeanPoincare` → DF `OriginalPhysicalVarianceSandwich` → DR `OriginalWilsonVarianceTwelveColorCoercivity` → CL `OriginalBoundedCoreKernelExactFrontier` → BW/BX `OriginalFullJointL2ContinuousBilinear` / `OriginalFullJointL2Quadratic` → **DV** `OriginalFullJointHaarRieszCoercivity`. All these shorthand names share the full `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar` prefix and `MGAP4D/MathlibAnalytic/` directory.

For the physical D12 spectrum, follow CA `OriginalPhysicalTwelveDirichletLoewner` → DS `OriginalWilsonFullJointL2PhysicalFrameCoercivity` → DT `OriginalPhysicalTwelveDirichletOperatorGap` → DU `OriginalPhysicalTwelveDirichletOrthogonalSpectrum`.

**Audit policy:** On theorem PRs verify original physical meanings, all changed Lean files **and their dependencies**, frozen Lean/mathlib pins, exact tested PR HEAD, success of targeted Lean CI plus its matching MCP receipt, and absence of new `sorry`/`admit`/axioms. Do not report warnings as zero when CI shows otherwise. On a **documentation-only** PR, change only README/ROADMAP; it moves branch HEAD but does not constitute a new mathematical theorem.
