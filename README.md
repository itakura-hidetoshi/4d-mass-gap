# MGAP4D — 4D Yang–Mills / genuine Wilson SU(2) Lean 4 formalization

**Original interacting Wilson theory · Gauss-law physical Hilbert space · Lean 4 + mathlib · Hidetoshi Itakura**

> **Research status, 2026-10-20 JST:** Verified finite-volume original-Wilson source detection, quantitative local and spatial GI response, and a constructive inverse of a genuine two-coordinate physical-response Gram. **The four-dimensional continuum Yang–Mills existence and positive mass-gap problem is not proved.** The finite-volume estimates below must not be reinterpreted as a volume-uniform continuum theorem.

**日本語要約：** 実際のSU(2) Wilson相互作用posteriorとGauss則に従う物理源を保持したまま、元の空間Wilson作用に対する**真正な二文脈GI行列式の非零性**をLMで証明した。その後、局所プラケットのGI二乗エネルギー、物理応答の空間平均・一次下界、真の応答Gram行列の正定値性・定量的行列式下界・逆写像の安定性、単一実プラケットの平均エネルギー以上の選択をMKまでLean 4で形式化した。**しかし体積一様の正のGIエネルギー密度、正のfine結合で任意Krylov深さの全物理源分離、真正endpoint源への推論移送、H1-C3強極限、連続体構成と質量ギャップは未解決**である。

**[Acceptance gates and next proofs → ROADMAP.md](ROADMAP.md)**

## 1. Theorem authority, pinned environment, and verified checkpoint

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Last verified theorem-bearing merge checkpoint (MK)** | [`92fe1141e68d545d1fb33e6bb30f6e35db5f5ba7`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/92fe1141e68d545d1fb33e6bb30f6e35db5f5ba7) |
| Latest verified theorem PR at this checkpoint | [#5740 — P4-Q2-MK](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5740), squash MERGED |
| Exact **tested source** SHA (distinct from squash SHA) | `bc1d8c3008b140bf13ffc44fff989c5d4b8ad68f` |
| [MK exact-head CI #39411635424](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39411635424) | SUCCESS; Lean **10820/10820**, MK changed-file warnings/errors **0/0**, four `#print axioms` reports, no `sorryAx`, MCP completion receipt SUCCESS |
| Pinned Lean | `leanprover/lean4:v4.30.0-rc2` (see `lean-toolchain`) |
| Pinned mathlib | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` (see `lake-manifest.json`) |
| Live branch | [re-observe the current theorem branch](https://github.com/itakura-hidetoshi/4d-mass-gap/tree/formal/real-hilbert-uniform-coercive-strong-limit) |

The checkpoint is deliberately **a dated theorem-bearing merge**, not a claim that the branch HEAD cannot advance when these documents or subsequent theorems merge. A documentation-only commit does **not** prove new mathematics. Order of evidence: **fresh authoritative HEAD → exact Lean declarations and their imports → CI at the exact source SHA and `#print axioms` → README/ROADMAP → historical discussions**. The repository's default `main` is **not** the theorem carrier.

## 2. Actual model: do not conflate these objects

1. **Original physical Wilson model.** The genuine interacting SU(2) spatial Wilson action, one-slab kernel, normalized joint ground-state/Perron transfer, and Gauss-law-invariant physical Haar-`L²` sources. Frozen `b = β_n` and fine `t = β_{n+1}` are distinct couplings.
2. **Two actual interacting posterior laws.** `p_{0,b}` and `p_{π,b}` are not independent Haar laws. SU(2) Haar is a reference measure for the actual densities, and pair-Haar integrations over genuine full boundary contexts are another operation.
3. **Actual signed source response.** `G_{H,b,e,z}(f)` is the original signed expectation/physical response of the true receiver under those two interacting posteriors. It retains joint half-density, transfer normalization and physical link insertion.
4. **Different operators and proof gates.** The original unnormalized Wilson Haar-reference `A_W`, normalized physical conditional-projection Dirichlet operator `D₁₂`, original signed GL/GI detector, finite-dimensional physical source Gram, and limiting physical time evolution are **different mathematical objects**. Restricted finite-volume positivity of one does not provide an absolute continuum mass gap for another.

In particular, **two different quantities historically called `Q` must be kept distinct**:

- `Q_post(b,e,z) = ∫(p_{0,b}-p_{π,b})² dν`: a *posterior density-contrast* norm in the earlier genuine GI bound.
- `Q_GI(H,b,e,e',z,z') = Σ_{p∈P_H} d_p²`: the *transfer-compensated original local GI-minor square energy* of LY onward. `Q_GI` in the equations below **never** denotes posterior contrast.

The compensation is purely scalar, not a change of physical law:
`d_p = ||T_{H,b}||² Δ_p`, where `Δ_p` is the actual original two-context local Wilson GI determinant. Its true underlying physical source remains `xU+yW_{H,p}U`.

## 3. What is proved: authentic Wilson source detection

The original **spatial** static two-context Wilson determinant is
\[
\Delta_W(z,z')=G_{e,z}(1)\,G_{e',z'}(W_H)-G_{e,z}(W_H)\,G_{e',z'}(1).
\]

- [JI–JK, #5656–#5657](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657): actual spatial minor definition, anchored centering, exact Haar-moment obstruction, and original fine-coupling derivative `M'_0=-Δ_W/2`.
- **[LM, original nonzero two-context minor](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoContextSpatialGIMinorNonzeroV5_LM.lean)**: for every fixed finite H, **b>0**, pair of actual physical links and prescribed initial boundaries, **some two genuine original interacting-Wilson contexts** yield `Δ_W≠0`. The former README/ROADMAP statement “original spatial nonzero GI minor OPEN” is **obsolete**. See `p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts`.
- **[LN–LP, true physical and local witness](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalPlaquetteGIWitnessV5_LO.lean)**: original constant-unit and Wilson spatial physical source planes, genuine local-plaquette GI minors, quantitative original physical two-source Frobenius coercivity and a real plaquette witness.
- [LS–LX, genuine transfer/Harnack estimates](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferNormalizationCompensatedCoercivityV5_LW.lean): original posterior/receiver norm, physical one-link joint-density Harnack and contrast envelope. The positive original contrast scale is
  \[
  E_b=e^{8b}(e^{16b}-e^{-16b})>0 \quad(b>0).
  \]
  Bounds on the compensated receiver are volume-independent *at fixed b*, but the resulting positive **coercivity floor** is not thereby uniform in H.

LM **closes the finite-volume spatial nonzero witness**, *not* all higher-Krylov source injectivity or continuum dynamics. A conditional small-positive-fine derivative consequence has to preserve its specific context, fine-coupling window and source; it does not extend automatically to all depths.

## 4. Quantitative genuine GI energy and physical spatial frame (LY–MK)

Fix a genuine finite H, `b>0`, physical links `e,e'`, and actual interacting-Wilson contexts `z,z'`. Define

\[
N_H=|\mathcal P_H|,\qquad
Q_{\rm GI}=\sum_{p\in\mathcal P_H}d_p^2,\qquad
k_{H,b}=\frac{Q_{\rm GI}/N_H}{10E_b^2}.
\]

These are computed from the **original finite plaquette carrier** and the **original two posterior GI determinants**. Let

\[
R_p(x,y)=G_{e,z}(xU+yW_{H,p}U)^2+
           G_{e',z'}(xU+yW_{H,p}U)^2.
\]

The true source is **p-dependent**: an average of these responses is not a single p-independent endpoint source.

| Stage / verified PR | Exact proved scope |
| --- | --- |
| **[LY, local square energy](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalGICompensatedSquareEnergyV5_LY.lean)** | Cancellation-free `Q_GI`; authentic positive-energy witness contexts; local max attaining `d_p² ≥ Q_GI/N_H` and original physical `κ_p ≥ Q_GI/(10N_HE_b²)`. This **mean-plaquette mechanism already occurs in LY**. |
| [LZ–MA, variance and original local ceiling](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCompensatedGIUniformLocalMomentBoundV5_MA.lean) | Exact mean/variance decomposition and `d_p² ≤ (4E_b²)²=16E_b^4` on every true plaquette; upper moment/variance bounds, **not** a uniform positive energy-density lower bound. |
| [MB #5729](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5729) | True energy-active original plaquettes `A={p : d_p² ≥ Q_GI/(2N_H)}` and their finite-H density floor. Duplicate exact-source CI recovery [#5730](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5730) added no new mathematical content. |
| [MC #5731](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5731) | Every actual active p has true positive original physical coercivity; verification-only [#5732](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5732) was closed **unmerged**. |
| [MD #5733](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5733), [ME #5734](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5734) | Active-to-full genuine spatial response `R_p` lower bounds; initial full response bound quadratic in `Q_GI/N_H`. |
| **[MF #5735](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5735)** | Eliminates the half-mean activity truncation: **linear** finite-H full original spatial response bound `k_{H,b}` via a pointwise original physical source inequality and exact finite sums. |
| [MG #5736](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5736), [MH #5737](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5737) | Exact physical 2×2 spatial-response Gram via polarization; Gram positivity and `det G≥kA≥k²>0` at real positive-energy contexts. |
| [MI #5738](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5738), [MJ #5739](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5739) | Constructive adjugate inverse; uniqueness, squared inverse stability, exact additivity/homogeneity and **two-input Lipschitz** bound for arbitrary real Gram dual coordinates at fixed original contexts. |
| **[MK #5740](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5740)** | Separate reusable theorems selecting **one actual p** with `d_p²≥Q_GI/N_H`, genuine `κ_p≥k` and `k(x²+y²)≤R_p(x,y)` for all real x,y at the same genuine contexts; refines/organizes LY's existing maximum-witness result, without a new physical assumption. |

Two particularly useful **already checked** finite-H inequalities are
\[
\boxed{\quad
k_{H,b}(x^2+y^2)\leq
\frac{1}{N_H}\sum_{p\in\mathcal P_H}R_p(x,y),\qquad
\exists p\in\mathcal P_H:\ k_{H,b}(x^2+y^2)\leq R_p(x,y).
\quad}
\]
When genuine `Q_GI>0`, `k_{H,b}>0`. The existential plaquette/witness may depend on H, b and the original contexts.

For the **same actual spatial response**, set
\[
A=\tfrac1{N_H}\sum_pR_p(1,0),\quad
C=\tfrac1{N_H}\sum_pR_p(0,1),\quad
B=\tfrac1{2N_H}\sum_p[R_p(1,1)-R_p(1,0)-R_p(0,1)].
\]
Then the exactly polarized original spatial Gram `G=(A\ B;\ B\ C)` satisfies
\[
\frac1{N_H}\sum_pR_p(x,y)=Ax^2+2Bxy+Cy^2,\qquad
G\succeq k_{H,b}I,\qquad
AC-B^2\geq k_{H,b}A\geq k_{H,b}^2>0.
\]
MI/MJ give a **fixed-context inverse** with
\[
G^{-1}(s,t)=
\left(\frac{Cs-Bt}{AC-B^2},\,\frac{At-Bs}{AC-B^2}\right),\qquad
k_{H,b}^{\,2}\|G^{-1}v-G^{-1}w\|_2^2\leq\|v-w\|_2^2.
\]

**Critical interpretation:** this is an original Wilson **spatial two-coordinate response frame**, with original `p`-dependent physical sources. It does **not** prove invertibility of the full physical transfer operator or positivity for all original physical Krylov sources; it is not a one-source endpoint theorem.

## 5. Distinct earlier finite-volume results

- The original Wilson Haar-reference `A_W` and normalized physical Dirichlet `D₁₂` have distinct finite-volume Riesz/Loewner/restricted-spectrum results: [#5440](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440), [#5472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472), [#5485](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485).
- [#5514, ES–ET](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514): the actual color count `L_c(H)=4(H+1)^3` and an H-dependent **relative** operator coefficient obstruction, not an absolute continuum-gap no-go.
- [#5574, GI–GL](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574): original two-interacting-posterior signed physical response lower certificate with *the genuine `Q_post`* in its denominator. Never substitute `Q_GI` for this different quantity.
- [#5601–#5639, HI–IR](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639): actual physical signed-source detectors, physical invisible subspace `I_phys=S(ker Φ)` and restricted visible quotient. Full signed-source positivity is conditional on eliminating this invisible sector. The zero-fine/all-depth and zero-depth/all-nonnegative-fine boundary cases are proved [#5621](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5621).
- [#5661–#5665, JO–JS](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665): genuine temporal-Wilson posterior contrast detection, original physical receiver covariance remainder and a conditional receiver-span obstruction. They remain useful **separate** theorems; the once-open *spatial* nonzero-witness gate was subsequently closed by LM rather than by silently assuming receiver-span membership.

## 6. Explicitly OPEN — the actual continuum proof obligations

1. **Uniform authentic signed-source information.** Even though a witness with `Q_GI>0` exists at each finite H, **no** positive uniform lower bound for `Q_GI/N_H` across H/spacing/scales and physically compatible contexts is proved. `E_b` and the coupling schedule also require control.
2. **Full physical source coverage and endpoint transport.** Neither a p-dependent two-source Gram nor its stable inverse proves the required source separation for **arbitrary positive fine coupling and every Krylov depth**. The zero-invisible-sector condition and the transfer of actual local source estimates to the **same genuine endpoint physical source family** are open.
3. **Spatial/scale summability.** Genuine interacting-Wilson receiver covariance and spatial tails must have appropriate localization and summable, volume-compatible constants; no Dobrushin substitute or independent-Haar conditional model may be silently introduced.
4. **H1-C1/C2/C3 strong limit**, including genuine coarse/fine compatibility and a single natural-time physical operator; physical-time semigroup, OS/Wightman reconstruction and full nontrivial continuum **4D Yang–Mills mass gap** are subsequent, separate open gates.

No single fixed-volume rank/Gram witness, positive finite-lattice spectral band, or `sorry`-free theorem resolves those continuum obligations. See the precise **[ROADMAP](ROADMAP.md)**.

## 7. Reproducing source and auditing proof integrity

Work from the **verified theorem-bearing MK checkpoint**, not default `main` or an unrelated docs-only SHA:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach 92fe1141e68d545d1fb33e6bb30f6e35db5f5ba7
cat lean-toolchain
# Optional when a compatible pinned cache is available:
lake exe cache get
# Dependency-aware build of the exact latest theorem-bearing leaf:
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalMeanEnergySinglePlaquetteV5_MK
# Full repository build is a separate, more expensive check:
# lake build
```

The file already contains four `#print axioms` commands. Check them and the exact-source [MK CI receipt](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39411635424). **No `sorryAx` was reported on these MK public theorems.** Some imported results inherit *previously known* finite-lattice `native_decide` axioms in addition to `propext`, `Classical.choice` and `Quot.sound`. Do not assert that all formal dependencies are axiom-free.

For a future theorem: inspect current canonical SHA, the **complete Lean file and its physical prerequisites**, the exact changed-source-head CI and public axioms; fix errors/warnings in changed files, verify the independent MCP CI completion receipt, then merge and re-observe the new canonical SHA. For README/ROADMAP-only updates the workflow should use its fast non-Lean path rather than rebuilding thousands of unchanged theorem modules.
