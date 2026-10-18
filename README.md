# MGAP4D — four-dimensional Yang–Mills formalization

Lean 4 / mathlib research on the **original SU(2) Wilson lattice theory**, its real physical Hilbert-space observables, and the mathematical obligations required for a four-dimensional continuum Yang–Mills theory with a mass gap.

**Research status: finite-volume results and genuine original-Wilson posterior/physical-receiver theorems are formalized; the continuum Yang–Mills existence and mass-gap problem remains OPEN.** In particular, positivity of a finite-volume form, nontriviality of a posterior test, and separation of *every* physical source are different claims.

> **Audited checkpoint — 2026-10-18 JST, P4-Q2-JS.**
> The sole authoritative theorem-carrier is `formal/real-hilbert-uniform-coercive-strong-limit`. The confirmed theorem-bearing merge/branch SHA after [PR #5665](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665) was
> **`d5316fe0a0cf96a8ab8a198bda280ac035585ab4`**.
> Its source `299eb09258efaa6d1e1c7683c1afa3f4945964a0` passed [exact-head CI #39098811665](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39098811665): **Lean 10754/10754**, changed-file warnings/errors **0**, all **5** new theorem axiom reports without `sorryAx`, MCP receipt **SUCCESS**.
> This is a **historically fixed proof checkpoint**, not a promise that the canonical HEAD will always be this SHA. This documentation update will itself advance the branch HEAD. Re-query the authoritative branch before relying on a SHA.

[Mathematical roadmap and proof obligations](ROADMAP.md) · [Original pre-rewrite technical record](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d5316fe0a0cf96a8ab8a198bda280ac035585ab4/README.md) · [Original pre-rewrite roadmap](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d5316fe0a0cf96a8ab8a198bda280ac035585ab4/ROADMAP.md)

## 1. Authority, environment, and reproducibility

| Item | Authoritative value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| Repository default `main` | **Not** the theorem carrier |
| Last theorem-bearing checkpoint | **P4-Q2-JS / PR #5665**, merge SHA `d5316fe0a0cf96a8ab8a198bda280ac035585ab4` |
| Lean | `leanprover/lean4:v4.30.0-rc2` |
| mathlib source in `lake-manifest.json` | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Latest theorem-source CI | [#39098811665](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39098811665) — **SUCCESS**, 10754/10754 |
| Exact-head MCP CI receipt | Job `117593807844` — **SUCCESS** |

**Evidence order:** fresh exact authoritative branch SHA → actual Lean declarations/proof terms at that SHA → exact-source CI, axiom output and MCP completion receipt → README/ROADMAP → historical claims. A green run at one source SHA does not certify different source content or the continuum problem.

To reproduce the current theorem-bearing endpoint, check out the **fresh authoritative branch** with its existing pinned manifest; do not silently upgrade mathlib:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch formal/real-hilbert-uniform-coercive-strong-limit
git pull --ff-only origin formal/real-hilbert-uniform-coercive-strong-limit
cat lean-toolchain
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverSpanObstructionV5_JS
```

The exact-JS CI used the repository's dependency cache and completed 10754/10754 jobs. The five newly printed theorem dependencies contain no `sorryAx` or new postulated axioms; the final two inherit **five existing finite-lattice `native_decide` axiom dependencies**. Do not conflate *zero warnings in changed JS source* with no pre-existing warnings elsewhere in the repository.

## 2. What has actually been proved

| Lane | Verified finite-volume achievement | What it does **not** establish |
| --- | --- | --- |
| Original Wilson joint-`L²` Riesz `A_W` and physical twelve-color Dirichlet `D12` (DR–EC) | Full finite-volume form/Loewner/spectral coercivity on the stated orthogonal sectors; separate operators with explicit normalizations | An H-/spacing-uniform continuum spectral gap or equality of `A_W` and `D12` |
| Genuine SU(2) geometry and relative-link witnesses (ED–ET) | Original physical relative-link gauge-invariant witnesses, exact selected support and `L_c(H)=4(H+1)^3`; a **relative** comparison bound `κ≤3/(H+1)^3` for the specified witness | A no-go for every continuum route or an absolute operator spectral gap |
| Signed fine/frozen physical source and original posterior GL detector (EU–GL) | Real signed-source quadratic identities, strictly positive **posterior contrast `Q`**, original two-posterior expectation-gap-square source-conditioned GL certificates | Strict GI detection of every nonzero physical source, uniform source frames or spatial covariance summability |
| Physical source synthesis versus original GI detector (GM–IV) | Real-linear genuine source synthesis `S` and full-context detector `Φ`; finite context certificates; exact physical invisibility/kernel/rank obstruction; zero-fine-beta and depth-zero special-case separation | `ker S = ker Φ` for arbitrary **positive fine beta and depth > 0** |
| Wilson Haar row and its GI first variation (IW–JI) | Real one-link `-I` Wilson-action contrast; nonconstant genuine Haar row for small positive beta; strong sup-norm/Haar-`L²` derivative; actual original-GI two-context minor's **static spatial Wilson** first derivative | A genuine **nonzero two-context static spatial GI determinant** |
| Original temporal SU(2) posterior (JK–JP) | Frozen-zero detector no-go, exact centered temporal log/density Taylor structure, strict original posterior detection of the literal temporal Wilson test at small positive frozen beta | Detection of a particular real physical Gauss-law source merely from temporal posterior separation |
| **True physical GI source receiver (JQ–JS)** | Exact original physical GI/pair-posterior bridge, Haar-centering and quantitative receiver covariance bound; algebraic genuine-receiver-span obstruction | Membership of temporal Wilson test in the physical receiver span, full spatial source separation, H1-C3 or a continuum gap |

All these assertions are relative to their actual Lean hypotheses and the original finite-volume model. The [roadmap](ROADMAP.md) separates the historical closed gates and outstanding obligations more finely.

### 2.1 Three mathematical objects that must remain distinct

1. **Original interacting Wilson physical joint law** `μ_W`, its genuine physical Hilbert space, and the original conditional posterior density rows `p_0,p_1`. Their difference `p_0-p_1` is tested against a source-dependent physical receiver; its Haar mean vanishes because both original laws are normalized.
2. **Independent reference Haar measures:** normalized compact SU(2) Haar is a common density/integration reference, and *outer pair-Haar* is a separate measure on boundary context pairs. Pair-Haar coordinate projections are **not** the physical interacting Wilson conditional expectations.
3. **Separate quadratic objects:** original unnormalized twelve-color Wilson-reference Riesz form `Q_W`/`A_W`; the normalized physical twelve-color Dirichlet `E12`/`D12`; the distinct original physical GI gap-square `M_GL`; and the literal source Haar-`L²` Gram `Q_src`. They cannot be interchanged merely because their finite-volume kernels or inequalities are related.

The actual physical source under adjacent scales uses **fine** `β(n+1)`; the frozen physical detector and posterior use **frozen** `β(n)`. No step sets them equal without an explicit theorem.

## 3. Current frontier: original GI detection of a physical source

### 3.1 Spatial Wilson first-order detector (IW–JI and JK)

For the genuine original one-slab Wilson Haar row,

```text
F_t(B) = ∫ exp(-t S_one-slab(A,B)) dHaar(A)
D_H(B) = F'_0(B) = -W_H(B)/2 - κ_H
```

JF proves the **uniform-in-B finite-H remainder**
`‖F_t-1-t D_H‖∞ ≤ (t M_H)^2` for small `|t M_H|`. JG promotes this to a **strong Haar-`L²` derivative**. JH passes that derivative through a bounded functional constructed from the actual frozen Wilson kernel, positive physical density and the difference of two ORIGINAL interacting posterior densities.

At two genuine link/full-boundary contexts `x,y`, JI defines the static original spatial-Wilson test determinant

```text
Δ_W(b;x,y) = G_(b,x)(1) G_(b,y)(W_H)
            - G_(b,x)(W_H) G_(b,y)(1).

M_t = G_(b,x)(1) G_(b,y)(F_t)
      - G_(b,x)(F_t) G_(b,y)(1).

M_0 = 0,  M'_0 = -Δ_W(b;x,y)/2.
```

If **`Δ_W(b;x,y)≠0` for some genuine contexts**, the original normalized physical unit/fine transfer minor is nonzero throughout a sufficiently small positive fine-coupling interval. **That static nonzero witness has NOT been constructed.** JK reformulates it using a genuine nonzero anchor, its centered spatial Wilson source, the actual common GI kernel, Riesz orthogonality and the original Haar moment; this is an obstruction criterion, not a witness.

### 3.2 Temporal posterior versus actual physical receiver (JL–JS)

JL proves that at **frozen `b=0`** the original posterior contrast and original GI detector vanish. JM–JN2 prove the genuine centered SU(2) temporal Wilson log/density perturbation and explicit small-`b` remainder. JO proves the temporal SU(2) test `D` has Haar mean zero and positive Haar variance `V_SU2>0`.

JP [#5662](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5662) proves that the **two original interacting normalized Wilson posteriors** strictly distinguish this particular temporal test for every right context/link, throughout a positive interval independent of finite spatial volume:

```text
ε_temporal = min(1/4, V_SU2 / (4 * 272 * exp(8))) > 0.

0 < b < ε_temporal
    ⇒ Gap_posterior,b(D) ≤ -(b/2) V_SU2 < 0.
```

**This does not prove the test `D` is a receiver of any given physical Hilbert source.** In JQ [#5663](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5663), for a genuine Gauss-law physical source `f`, physical link `e` and full spatial pair-context `z`, the actual source receiver `F_(b,f,e,z)` satisfies

```text
GI_b(f,e,z) = -Gap_posterior,b(F_(b,f,e,z)) / q_b(z),
q_b(z) > 0.
```

JR [#5664](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664) removes only the receiver's normalized SU(2) Haar mean:
`F_c=F-∫F dHaar`. This preserves the **exact** original GI response and its temporal covariance. For `0≤b≤1/4`, its sharper genuine-source bound is

```text
| q_b(z) GI_b(f,e,z) - b ∫ F_c(g) D(g) dHaar(g) |
    ≤ ||F_c||∞ · 272 exp(8) · b².
```

Thus a strictly dominating **actual centered physical receiver–temporal Wilson covariance** is sufficient for a nonzero physical GI response. It is a *condition*, not a constructed witness.

JS [#5665](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665) takes, at fixed right boundary/link, the real algebraic span of all genuine physical receiver functions (`f` and left boundary varying), **plus constants**. The genuine posterior test annihilates constants. JS proves:

- If every actual physical GI response there vanishes, the temporal Wilson test `D` **does not belong** to that receiver span.
- Conversely, if the temporal test **does belong** to that span, some actual physical GI response is nonzero in JP's weak positive coupling interval.

It **does not** prove `D` belongs to the span, nor does it close JI/JK's distinct static *spatial* Wilson two-context minor.

## 4. Remaining mathematical obligations

The primary new task is **physical source detection, not just posterior sensitivity**. Analyze the actual centered Wilson receiver `F_c` against the true temporal test `D`, and/or construct concrete contexts with `Δ_W(b;x,y)≠0`. A source-independent test cannot replace the physical source receiver.

Other unresolved gates include: positive-fine-coupling higher-depth source separation; a positive physical source-norm GL lower bound on the **whole** actual source span; H/n/depth/spacing-uniform constants and signed spatial summability; compatible strong fine/coarse transfer reconstruction (H1-C3); nontrivial continuum time and OS Hamiltonian; and the continuum four-dimensional Yang–Mills existence and mass gap. See [ROADMAP.md](ROADMAP.md).

**Do not revive the unsuccessful Dobrushin reconstruction as the default proof route.** Earlier H1-D5 and specific Dobrushin scaling no-go results concern their stated constructions, not all conceivable continuum methods.

## 5. Reading the newest proof sources

All of the following live under `MGAP4D/MathlibAnalytic/` and use prefix
`PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar`:

| Lane | Lean suffix | PR |
| --- | --- | --- |
| Strong Haar-`L²` Wilson derivative | `OriginalWilsonStrongHaarL2DerivativeV5_JG.lean` | [#5654](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5654) |
| Genuine bounded frozen-Wilson GI Riesz functional | `OriginalWilsonFiberRieszDerivativeV5_JH.lean` | [#5655](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5655) |
| Static spatial Wilson two-context minor | `OriginalGISpatialActionMinorTangentV5_JI.lean` | [#5656](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5656) |
| Anchored spatial Wilson common-kernel obstruction | `OriginalStaticGISpatialKernelV5_JK.lean` | [#5657](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657) |
| Frozen `b=0` posterior no-go | `OriginalPosteriorWeakFrozenNoGoV5_JL.lean` | [#5658](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5658) |
| Posterior log and density Taylor | `OriginalPosteriorCenteredLogTangentV5_JM.lean` / `OriginalDensityMinorTaylorV5_JN.lean` / `OriginalPosteriorHaarMinorReconstructionV5_JN2.lean` | [#5659](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5659), [#5660](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5660) |
| Temporal Wilson centering and posterior separation | `OriginalTemporalWilsonHaarCenterV5_JO.lean` / `OriginalTemporalPosteriorTestDetectionV5_JP.lean` | [#5661](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5661), [#5662](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5662) |
| Original physical source receiver and centering | `OriginalGIPhysicalReceiverTemporalCovarianceV5_JQ.lean` / `OriginalGICenteredReceiverTemporalCovarianceV5_JR.lean` | [#5663](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5663), [#5664](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664) |
| **Actual receiver-span obstruction** | **`OriginalGIPhysicalReceiverSpanObstructionV5_JS.lean`** | **[#5665](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665)** |

Recheck all Lean theorem types and current branch SHA before claiming any new nonvanishing, rank or uniformity result. Earlier finite-volume proof chains and their precise historical statements remain retrievable from Git history and the [pre-rewrite README](https://github.com/itakura-hidetoshi/4d-mass-gap/blob/d5316fe0a0cf96a8ab8a198bda280ac035585ab4/README.md).

**Verification rule:** full changed-source inspection, fixed Lean/mathlib pins, actual theorem types and `#print axioms`, exact-PR-head CI success, changed-file warnings/errors, MCP exact-SHA receipt, and **post-merge canonical HEAD reobservation**. Documentation-only commits do not count as new theorems.
