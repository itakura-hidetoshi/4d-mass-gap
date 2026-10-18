# MGAP4D — proof roadmap after P4-Q2-JS

**Updated 2026-10-18 JST · Sole theorem source: `formal/real-hilbert-uniform-coercive-strong-limit` · Snapshot SHA `d5316fe0a0cf96a8ab8a198bda280ac035585ab4`**

**日本語要約：** 原Wilson作用の有限体積形式化と真正相互作用posteriorの時間方向非零検出は成功している。次の中心課題は **空間Wilson作用を真正GI物理受信関数が非零に検出すること**。その後に正のfine結合・任意Krylov深さでの全物理源分離、体積一様な可和性、H1-C3強極限、物理時間／OS再構成、連続体質量ギャップを証明する。各段階は別々の公理・定理要件を持ち、前段を飛び越して「完全なYang–Mills証明」と主張しない。

See [README.md](README.md) for physical notation, the full original-posterior inequality, pinned Lean environment and the explicit distinction between finite-volume and continuum results.

## 0. Authority and reproducibility

| Field | Exact historical checkpoint |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only authoritative theorem branch** | `formal/real-hilbert-uniform-coercive-strong-limit` — not the repository default `main` |
| Latest canonical theorem HEAD at this review | [`d5316fe0a0cf96a8ab8a198bda280ac035585ab4`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/d5316fe0a0cf96a8ab8a198bda280ac035585ab4) |
| Latest merged theorem PR | [#5665 (JS)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665) |
| Exact tested **source** HEAD for JS | `299eb09258efaa6d1e1c7683c1afa3f4945964a0` (not the squash SHA) |
| JS [CI #39098811665](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39098811665) | **SUCCESS**; 10754/10754 Lean jobs; Changed Lean and MCP completion receipt SUCCESS |
| JS `#print axioms` | 5/5 printed; no `sorryAx` or new postulated axiom, new-file warning/error 0/0; certain results inherit previously identified finite-grid `native_decide` axioms |
| Lean / mathlib | `leanprover/lean4:v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |

Authority ordering for each mathematical assertion: **fresh exact canonical branch SHA → actual Lean theorem statements/proofs and imported premises → exact-source-head CI with axiom output → README/ROADMAP explanations → older conversations and comments**. Recheck SHA on every new session. A docs-only merge does not introduce mathematical evidence.

## 1. Proof-state matrix: CLOSED means only the stated scope

| Track / gates | Proven in the actual Lean development | Remaining obstruction |
| --- | --- | --- |
| **Physical posterior and transfer model** | Actual normalized interacting Wilson one-slab conditional laws and Perron/transfer factors; genuine gauge-invariant physical sources and right-link insertion [GI–GN #5571–#5577](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5577) | Do not replace either interacting conditional posterior by independent Haar or drop density/vacuum weights |
| **Finite original Wilson Haar-`L²` `A_W`** | Original Riesz full-`L²` bounded quadratic, self-adjoint operator, Loewner comparison and fixed-model positive spectrum [CO, DV–EC #5440, #5473–#5485](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485) | H-/spacing-independent lower bound and continuum transfer |
| **Physical `D₁₂`** | Normalized original physical Wilson Dirichlet operator, positive `V^\perp` spectrum [DS–DU #5470–#5472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472) | Not the same as `A_W` or the signed adjacent-scale source Gram; no continuum gap |
| **Relative color geometry** | Real SU(2) color count `L_c(H)=4(H+1)^3` and **relative** coefficient bound `κ≤3/(H+1)^3` [ES–ET #5513–#5514](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514) | Do not claim an absolute spectral-gap no-go from a relative comparison |
| **Original GL/source `Δ²/Q` bound** | Real two-original-posterior GI expectation differences, integrable pair-Haar physical Gram Rayleigh bound [GI–GL #5571–#5574](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574) | `Q>0` does not prove `Δ(f)≠0` for every physical source |
| **All-context GI detector and source quotient** | Finite authentic-context kernel certificates; actual source Gram/rank; invisible subspace `I_phys=S(ker Φ)` and visible orthogonal quotient [HI–IR #5601–#5639](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639) | For positive fine coupling and higher `r`, prove `I_phys=0`; finite quotient positivity alone is weaker |
| **Endpoints / specific positive-fine witness** | `ker S=ker Φ` for **fine `t=0` at all finite `r`** and **`r=0` at all fine `t≥0`** [HZ–IB #5619–#5621](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5621); particular original positive-fine rank-one innovation interval [#5365 Z2](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5365) | These do not establish arbitrary-depth, positive-fine, all-source detection or H/n/r-uniformity |
| **Spatial Wilson physical source** | Genuine `W_H` nonconstant; its anchored centered Haar-`L²` class is nonzero; exact spatial GI static minor and Haar integral obstruction [JI–JK #5656–#5657](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657) | **OPEN**: an actual second physical context where `Δ_W(x,y)≠0` |
| **Original temporal Wilson posterior** | Haar mean of literal SU(2) temporal `D` is zero; genuine original posterior contrast has a volume/link/right-context-independent strict negative test-gap at sufficiently small `b>0` [JO–JP #5661–#5662](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5662) | Temporal sensitivity **does not itself** make the spatial GI source detectable |
| **Real source-to-temporal bridge** | Actual original physical receiver and normalizing weight; Haar-centered quadratic error and sufficient correlation criterion [JQ–JR #5663–#5664](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664) | **OPEN**: prove its required covariance for the actual spatial Wilson source, respecting `b`-dependence |
| **Actual physical receiver-span obstruction** | If all actual physical GI responses vanish, literal temporal `D` is outside span of actual physical link receivers + constants; `D` membership implies a nonzero GI witness [JS #5665](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665) | **OPEN**: establish physical receiver representation or otherwise prove a nonzero original GI response |
| **Cross-scale/continuum** | Several finite-volume and limited source-subspace certificates exist | **OPEN**: uniform signed source estimates, C1/C2/C3, H2/H3/H4 and the 4D continuum gap |

## 2. Exact current mathematical frontier: genuine spatial Wilson GI detection

Use fixed finite spatial `H`, positive *frozen* Wilson coupling `b`, true physical link `e` and two genuine boundary contexts `x,y`. Let `W_H` be the **original spatial Wilson action** and `G_x`, `G_y` the **actual** GI Riesz/expectation response functionals for the original interacting posteriors.

The decisive original static determinant is

$$
\Delta_W(x,y)
 =G_x(1)\,G_y(W_H)-G_x(W_H)\,G_y(1).
$$

From JK, when `G_x(1)≠0` one can set `c_x=G_x(W_H)/G_x(1)` and rewrite

$$
\Delta_W(x,y)=G_x(1)\,G_y(W_H-c_x1).
$$

Crucially, `W_H-c_x1\ne0` in the true spatial Haar-`L²`. Its image under `G_y` may nevertheless vanish for all `y`. JK reduces precisely this obstruction to one integral of the **unchanged** original Wilson transfer, joint square-root density and two authentic interacting posterior laws.

**Acceptance gate S — still OPEN:** supply at least one actual `H,b,e,e',x,y` with `b>0`, `G_x(1)≠0` and `G_y(W_H-c_x1)≠0`, or prove a stronger fully quantified theorem. No free two-context rank, generic physical detector or substituted independent-Haar posterior may be assumed.

**Once gate S is proved:** JI already provides the real raw fine-coupling derivative `M'_0=-\Delta_W/2` and normalized-minor continuation to a sufficiently small positive fine-`t` interval **for that genuine physical pair of contexts**. This will not automatically prove source separation at every Krylov depth, or any H-uniform bound.

## 3. Two complementary original-Wilson routes to gate S

### S1 — directly evaluate the actual centered spatial-Wilson moment

Use JK's literal original two-layer Haar formula. Show the anchored nonzero `L²` source has a nonzero pairing with at least one **actual** second-context Wilson Riesz representer. Key obligations:

1. Retain the original source `W_H-c_x1`, frozen coupling, Wilson kernel `K_b`, physical link update, joint half-density, and the difference `p₀,b-pπ,b`.
2. Prove the sign/nonvanishing of one explicit original double integral, via symmetry, an exact SU(2) calculation, or a controlled coupling expansion with justified continuity/remainder.
3. Prove all prefactors/normalizations strictly nonzero in the same physical context; transport the nonzero moment to `\Delta_W(x,y)≠0` using JK's established equivalence.

**Obstruction:** nonconstancy of `W_H` or nonzero posterior contrast is **not** sufficient without a nonzero cross-pairing.

### S2 — compute the covariance of an actual physical receiver with temporal `D`

JO–JP prove `\int D\,d\nu=0`, `V_{\mathrm{SU(2)}}=\int D^2d\nu>0` and a uniform weak-frozen-coupling window. JQ–JR show that with the **actual centered Gauss-law receiver** `F_c=F_{b,f,e,z}-\int F_{b,f,e,z}d\nu` and physical normalization `q_b(z)>0`,

$$
\left|
q_b(z)\,G_b(f,e,z)-b\int F_c(g)D(g)\,d\nu(g)
\right|
\le Cb^2\|F_c\|_\infty,\qquad C=272e^8.
$$

A sufficient nonzero condition for `b>0` is

$$
\left|\int F_cD\,d\nu\right|
> Cb\,\|F_c\|_\infty .
$$

This criterion is **not yet verified** for a spatial Wilson source and a genuine choice of `e,z`. The receiver **depends on `b`**, so proving only that an arbitrary, artificial fixed continuous test is correlated with `D` is invalid. If the authentic centered receiver vanishes at `b=0`, identify its first nonzero coefficient and control the error at the **same order**; simple first-order posterior sensitivity need not dominate the remainder by itself.

JS supplies another rigorous path. Define `\mathcal R_{b,e,B}` as the *algebraic* real span of genuine physical receivers over all physical Gauss-law Hilbert sources `f` and left boundary contexts `A` at fixed right context `B`/link `e`, plus constants. For `0<b<\rho=\min(1/4,V_{\mathrm{SU(2)}}/(4C))`,

$$
\Big[\forall f,A,\ G_b(f,e,(A,B))=0\Big]
\;\Longrightarrow\; D\notin\mathcal R_{b,e,B}.
$$

Hence `D\in\mathcal R_{b,e,B}` would force some genuine physical GI response to be nonzero. **Membership is still unproved**. It is a sufficient route, not a hidden assumption and not automatically the stronger two-context spatial-Wilson `\Delta_W` result.

**Acceptance gate R — still OPEN:** either prove a true centered-receiver covariance satisfying the explicit JR threshold, or prove actual receiver-span membership as required by JS. Then ensure the nonzero detected physical source is **the source needed for spatial gate S**, not just an unrelated GI witness.

## 4. Positive fine coupling, all-depth source geometry

At frozen `b_n>0`, denote by `S_{n,r}` the **actual** finite signed physical Krylov source synthesis and by `\Phi_{n,r}` the **original two-interacting-Wilson-posterior** joint GI detector. The exact physical invisible sector is `I_{\mathrm{phys}}=S_{n,r}(\ker\Phi_{n,r})`.

**Already CLOSED under their exact hypotheses:**

- `t_{n+1}=0`: all finite `r` have `\ker S_{n,r}=\ker\Phi_{n,r}`.
- `r=0`: all `t_{n+1}\ge0` have that equality.
- For any fixed finite model, the *visible* orthogonal subspace has positive original GL/source comparison; a global positive original GL/source-norm lower bound on all actual synthesized sources is **equivalent** to `I_{\mathrm{phys}}=0`.
- Historical Z2 [#5365](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5365) establishes a legitimate **specific** one-sided positive-fine innovation witness.

**Acceptance gate F — still OPEN:** for genuinely positive fine `t_{n+1}` and arbitrary finite `r>0`, prove `\ker S_{n,r}=\ker\Phi_{n,r}` (or identify explicit unavoidable invisible sources and a replacement physical subspace) using literal physical Wilson sources. Thereafter extract model-dependent positive `c_{H,b,t,r}`, distinguishing mere existence from an explicit or uniform coefficient.

Do **not** elevate zero-selector rays, individual rank-one perturbations, generic finite-dimensional anti-Lipschitz quotients, or `\ker\Phi\supseteq\ker S` into an all-source positive-fine theorem.

## 5. Spatial and scale-uniform quantitative gates

Fixed-volume spectral gaps for `A_W` and `D_{12}`, positive posterior-density separation and fixed-source nonzero moments are **not** scale-uniform signed-source coercivity.

| Gate | Necessary next evidence | Status |
| --- | --- | --- |
| **U1: genuine signed Wilson source bounds** | Estimate actual linkwise `\Delta_{b,e,F}` and covariance/Gram for arbitrary signed physical inputs, not only absolute oscillation envelopes | OPEN in uniform form |
| **U2: spatial summability** | Sum physical receiver tails/correlations over original `24(H+1)^3` spatial links with controlled H-independent or explicitly summable constants; prove localization rather than assuming it | OPEN |
| **U3: depth-uniform transfer** | Control all Krylov mode norms and relevant error sections uniformly in `r` while keeping frozen `b_n` distinct from fine `t_{n+1}` | OPEN |
| **U4: lattice spacing / scale** | Construct a legitimate scale schedule `b_n,t_{n+1}` and estimates independent of H/spacing or summable with the required weights | OPEN |
| **Compatibility guard** | ES–ET's decay of **relative** `A_W/D_{12}` comparison must not be misread as an absolute continuum-gap impossibility | PROVED limitation; alternative route needed |

Avoid restarting a Dobrushin reconstruction as the default plan; earlier restricted no-go results target that method, **not** every approach to continuum Yang–Mills. Do not assume original interacting conditional projections commute merely because pair-Haar reference coordinate projections do.

## 6. H1-C3 and continuum construction — separate OPEN proof gates

| Gate | Required theorem before calling it closed |
| --- | --- |
| **C1 — physicality / marginal descent** | Explicit coarse/fine common physical marginal; physical Gauss-law compatibility and no leakage from the genuine physical Hilbert space |
| **C2 — actual transfer/reconstruction** | Vector-wise control for original fine evolution/reconstruction against coarse physical transfer; strong convergence to a common physical operator on the needed source family |
| **C3 — trajectory summability** | A concrete `b_n` trajectory and summably controlled errors (including weights such as `|b_{n+1}-b_n|`), sufficient to close H1-C3 without a surrogate conditional posterior |
| **One natural-time structure** | Multi-time operators are powers/semigroup elements of **one** limiting physical operator, not unrelated pointwise limits |
| **H2 — physical time** | Actual spacing-scaled strongly continuous semigroup, positive self-adjoint generator and nontrivial excitations |
| **H3 — OS/Wightman reconstruction** | Continuum reflection positivity, localization, gauge-invariant observables, vacuum and field axioms, with correct reconstruction and spectral support |
| **H4 — 4D mass gap** | Full continuum nontrivial four-dimensional Yang–Mills existence plus strictly positive physical energy–momentum spectral gap, with scale/renormalization dependence controlled |

Every row in this section remains **OPEN**. Positive `A_W`/`D_{12}` finite-volume spectral bands and even a new finite-volume spatial GI witness would not close these by themselves.

## 7. Verifiable Lean theorem pointers and immediate work order

All paths begin with `MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar` and end in `.lean`:

| Priority | Exact file suffix | Key formally checked fact |
| --- | --- | --- |
| **1 — prerequisite** | `OriginalStaticGISpatialKernelV5_JK` | `p4Q2JK_originalSpatialMinor_ne_iff_actualHaarMoment_ne`; exact authentic second-context obstruction |
| **2 — positive-fine consequence** | `OriginalGISpatialActionMinorTangentV5_JI` | Literal spatial minor `\Delta_W` and conditional fine-coupling derivative bridge |
| **3 — temporal witness** | `OriginalTemporalPosteriorTestDetectionV5_JP` | `p4Q2JP_originalWilsonTemporalTestGap_strictNegative_uniform` |
| **4 — true physical receiver** | `OriginalGIPhysicalReceiverTemporalCovarianceV5_JQ` | `p4Q2JQ_originalPhysicalGI_temporalCovariance_quadratic` |
| **5 — improved covariance** | `OriginalGICenteredReceiverTemporalCovarianceV5_JR` | `p4Q2JR_originalPhysicalGI_centeredTemporalCovariance_quadratic` |
| **6 — current end point** | `OriginalGIPhysicalReceiverSpanObstructionV5_JS` | `p4Q2JS_temporalWilson_not_mem_physicalReceiverSpan_of_allGI_zero` and existential conditional GI witness |

Minimal exact JS compilation (after checking out the **current observed authoritative commit**, not default `main`):

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach d5316fe0a0cf96a8ab8a198bda280ac035585ab4
lake exe cache get              # optional pinned mathlib cache, when available
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGIPhysicalReceiverSpanObstructionV5_JS
```

For a changed Lean theorem, the proof-integrity checklist is: pin exact canonical SHA; inspect **full file, relevant definitions, imported prior statements and intended mathematical scope**; reuse pinned mathlib; build the exact source HEAD; resolve all changed-file warnings and errors; inspect every new `#print axioms` result for `sorryAx` and separately identify *inherited* `native_decide` finite-grid axioms; confirm MCP CI receipt for the **same** source SHA; then merge to the sole theorem carrier and reobserve its new SHA. No `sorry`/`admit`/fresh postulated `axiom`, independent-Haar conditional substitute, or artificial frame assumption.

## 8. Historical milestones without repeating outdated checkpoints

- **Physical Wilson joint/operator groundwork:** original nonperturbative construction, `A_W`, `D_{12}`, true six-color geometry and distinct pair-Haar reference — [#5440](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440), [#5472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472), [#5485](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485), [#5514](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514).
- **Authentic signed physical-source posterior certificate:** [#5574 (GL)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574), [#5606 (HM)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5606), [#5619–#5639 (HZ–IR)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639).
- **Historical restricted positive-fine innovation:** [#5365 (Z2)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5365).
- **Current spatial/temporal frontier:** [#5656 (JI)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5656), [#5657 (JK)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657), [#5662 (JP)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5662), [#5663 (JQ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5663), [#5664 (JR)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5664), [#5665 (JS)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665).

Full older chronological detail, including prior theorem-source SHA/CI results and historical no-go qualifications, remains available in the Git history of README.md and ROADMAP.md. **Always prefer current Lean source over historical prose.**
