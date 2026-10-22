# MGAP4D — 4D Yang–Mills / genuine Wilson SU(2) Lean 4 formalization

**Original interacting Wilson theory · Gauss-law physical Hilbert space · Lean 4 + mathlib · Hidetoshi Itakura**

> **Research status, 2026-10-22 JST:** Only the original two interacting SU(2) Wilson posteriors, physical Gauss-law Hilbert source and Perron half-density are used. Local spatial GI (LM–MK), true signed Gaussian kernel (NT–OC), physical source–receiver correspondence (OD), real physical U two-row floor (OE), right-Krylov zero-selector U transport (OF), fixed-context all-depth two-row GI modal bound (OG), and fixed one-row half-density bound/kernel finrank r (OH) are formally proved. **OI now provides an EXACT decomposition of every actual right-Krylov physical source into a detector-null-at-one-real-context remainder and a scalar multiple of the genuine unit source U**, retaining the original HF/HJ/OD operators. A single receiver kernel is **not** the global invisible physical sector. All-coefficient positive-fine GI injectivity, uniform U0, scale-compatible endpoint, H1-C3 and continuum mass gap remain OPEN.

**日本語要約：** 元の二つの相互作用Wilson posterior・Gauss-law源・Perron半密度を保ち、LM〜MKの物理空間GI、NT〜OCの時間Gaussian、ODの本来のposterior差分と物理受信器の一致、OEの同一物理源U強制性、OFの真正Krylov零次選択源＝U、OGの同じ文脈を使う全深さ下界、OHの真の一行の半分下界・正確な係数核次元r・各深さの開検出近傍を形式化した。**OI #5794**では任意の実right-Krylov係数aを `a=k_r(a)+t_r(a)a₀`（真正一行検出器でkが消える）と分解し、実際のHJ物理源合成写像で `S(a)=S(k_r(a))+t_r(a)U` を厳密証明。ODの同じ真正signed二posterior受信器が物理残差を選択した一文脈で消すことも証明した。全文脈の物理不可視性・正fine全係数源単射性・体積一様U0・共通endpoint・連続体4D質量ギャップは依然OPEN。

**[Acceptance gates and next proofs → ROADMAP.md](ROADMAP.md)**

## 1. Theorem authority, pinned environment, and verified checkpoint

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Last verified theorem-bearing merge checkpoint (OI)** | [`e43726d7d3ec770c2fed93cfb0d1559359d6d701`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/e43726d7d3ec770c2fed93cfb0d1559359d6d701) |
| Latest verified theorem PR at this checkpoint | [#5794 — P4-Q2-OI](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5794), squash MERGED; [#5793 — OH](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5793) also MERGED |
| Exact **tested source** SHA (distinct from squash SHA) | `0f086478b6eded1b0694cf579cfab9fbd6c7ecd6` (OI PR source) |
| [OI exact-head CI #39731413087](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39731413087) | SUCCESS; Lean **10870/10870**, changed OI warnings/errors **0/0**, six `#print axioms` reports without `sorryAx`, independent MCP completion receipt SUCCESS. **5/6** use only `propext`, `Classical.choice`, `Quot.sound`; one same-context all-depth existence result inherits previously documented finite-lattice `native_decide` axioms. |
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
$$
\Delta_W(z,z')=G_{e,z}(1)\,G_{e',z'}(W_H)-G_{e,z}(W_H)\,G_{e',z'}(1).
$$

- [JI–JK, #5656–#5657](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5657): actual spatial minor definition, anchored centering, exact Haar-moment obstruction, and original fine-coupling derivative `M'_0=-Δ_W/2`.
- **[LM, original nonzero two-context minor](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoContextSpatialGIMinorNonzeroV5_LM.lean)**: for every fixed finite H, **b>0**, pair of actual physical links and prescribed initial boundaries, **some two genuine original interacting-Wilson contexts** yield `Δ_W≠0`. The former README/ROADMAP statement “original spatial nonzero GI minor OPEN” is **obsolete**. See `p4Q2LM_originalSpatialWilsonGIMinor_exists_nonzero_contexts`.
- **[LN–LP, true physical and local witness](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalLocalPlaquetteGIWitnessV5_LO.lean)**: original constant-unit and Wilson spatial physical source planes, genuine local-plaquette GI minors, quantitative original physical two-source Frobenius coercivity and a real plaquette witness.
- [LS–LX, genuine transfer/Harnack estimates](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTransferNormalizationCompensatedCoercivityV5_LW.lean): original posterior/receiver norm, physical one-link joint-density Harnack and contrast envelope. The positive original contrast scale is
  $$
  E_b=e^{8b}(e^{16b}-e^{-16b})>0 \quad(b>0).
  $$
  Bounds on the compensated receiver are volume-independent *at fixed b*, but the resulting positive **coercivity floor** is not thereby uniform in H.

LM **closes the finite-volume spatial nonzero witness**, *not* all higher-Krylov source injectivity or continuum dynamics. A conditional small-positive-fine derivative consequence has to preserve its specific context, fine-coupling window and source; it does not extend automatically to all depths.

## 4. Quantitative genuine GI energy and physical spatial frame (LY–MK)

Fix a genuine finite H, `b>0`, physical links `e,e'`, and actual interacting-Wilson contexts `z,z'`. Define

$$
N_H=|\mathcal P_H|,\qquad
Q_{\rm GI}=\sum_{p\in\mathcal P_H}d_p^2,\qquad
k_{H,b}=\frac{Q_{\rm GI}/N_H}{10E_b^2}.
$$

These are computed from the **original finite plaquette carrier** and the **original two posterior GI determinants**. Let

$$
R_p(x,y)=G_{e,z}(xU+yW_{H,p}U)^2+
           G_{e',z'}(xU+yW_{H,p}U)^2.
$$

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
$$
\boxed{\quad
k_{H,b}(x^2+y^2)\leq
\frac{1}{N_H}\sum_{p\in\mathcal P_H}R_p(x,y),\qquad
\exists p\in\mathcal P_H:\ k_{H,b}(x^2+y^2)\leq R_p(x,y).
\quad}
$$
When genuine `Q_GI>0`, `k_{H,b}>0`. The existential plaquette/witness may depend on H, b and the original contexts.

For the **same actual spatial response**, set
$$
A=\tfrac1{N_H}\sum_pR_p(1,0),\quad
C=\tfrac1{N_H}\sum_pR_p(0,1),\quad
B=\tfrac1{2N_H}\sum_p[R_p(1,1)-R_p(1,0)-R_p(0,1)].
$$
Then the exactly polarized original spatial Gram `G=[[A,B],[B,C]]` satisfies
$$
\frac1{N_H}\sum_pR_p(x,y)=Ax^2+2Bxy+Cy^2,\qquad
G\succeq k_{H,b}I,\qquad
AC-B^2\geq k_{H,b}A\geq k_{H,b}^2>0.
$$
MI/MJ give a **fixed-context inverse** with
$$
G^{-1}(s,t)=
\left(\frac{Cs-Bt}{AC-B^2},\,\frac{At-Bs}{AC-B^2}\right),\qquad
k_{H,b}^{\,2}\|G^{-1}v-G^{-1}w\|_2^2\leq\|v-w\|_2^2.
$$

**Critical interpretation:** this is an original Wilson **spatial two-coordinate response frame**, with original `p`-dependent physical sources. It does **not** prove invertibility of the full physical transfer operator or positivity for all original physical Krylov sources; it is not a one-source endpoint theorem.

## 5. Original SU(2) Wilson Gaussian, physical GI receiver and exact Krylov source decomposition: NT–OI

For the **unchanged original SU(2) temporal Wilson section** on true holonomies `x,g ∈ SU(2)`, with the already-proved real-eight feature `J`,

$
K_b(x,g)=\exp(b\chi(x^{-1}g))
=e^b\exp\bigl(-\tfrac b4\|J(x)-J(g)\|^2\bigr),\qquad b>0.
$

| Verified stage | Exact theorem-bearing content |
| --- | --- |
| [NT–NX, #5776–#5780](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5780) | Genuine signed Wilson–Perron coordinate moments, all-degree character Gram expansion, finite double-action energy identities, bounded Banach double signed functional and convergent exponential. |
| **[NY #5781](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedGaussianStrictV5_NY.lean)** | For **every** nonzero continuous real linear functional `L` on `C(SU(2),ℝ)`, the **complete** Gaussian double signed energy `T_L(K_b)>0` for all `b>0`. This specializes to strict positivity of the **original Wilson–Perron signed receiver's local Haar variance**; **not** to an arbitrary physical GI covariance. |
| **[NZ #5782](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianKernelSpanDenseV5_NZ.lean)** | By Hahn–Banach, `closure(span_ℝ {K_b(x,·) : x∈SU(2)}) = C(SU(2),ℝ)` for each fixed `b>0`; linear **span**, not merely a generated algebra. |
| **[OA #5783](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianAllFiniteStrictGramV5_OA.lean)** | For every finite *injective* family of genuine SU(2) holonomies and every nonzero real coefficient vector, `Σᵢⱼ aᵢ aⱼ K_b(xᵢ,xⱼ)>0`; finite point selectors establish nonzero signed evaluation, without rank assumptions. |
| **[OB #5784](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianMatrixPosDefV5_OB.lean)** | Literal original Gram is `Matrix.PosDef`, `IsUnit`, has nonzero determinant, and has `PosDef` inverse in the pinned mathlib. |
| **[OC #5785](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGaussianFiniteInterpolationV5_OC.lean)** | At any finite set of distinct original SU(2) points and for any target vector `v`, coefficients `c=v ᵥ* M⁻¹` give `f(g)=Σⱼ cⱼK_b(xⱼ,g)` with **exactly** `f(xᵢ)=vᵢ`. Finite sections are linearly independent. |
| **[OD #5787](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwoPosteriorGaussianSeparationV5_OD.lean)** | The original two interacting Wilson posterior conditional density contrast `D=p₀−pπ` defines a **nonzero** real bounded signed functional `L_D(v)=∫v(g)D(g) dμ_Haar`. Its self-pairing is the **exact original** posterior squared Haar distance (GA/FX lower bound); NY gives positive complete signed Gaussian energy and an original Wilson temporal kernel section distinguishing the two posterior laws. **Exact original physical GI compatibility:** `Δ_GI(f;e,z) = L_{D(H,b,z.right,e)}(R_f(z,·))` for every actual Gauss-law physical Hilbert source `f`, with `R_f` the **unchanged FF signed receiver fiber**. Its general nonzero evaluation for physical `f` is NOT proved. |

| **[OE #5789](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSignedReceiverNonannihilationV5_OE.lean)** | Exact original FF receiver two-row signed functional square equals the genuine MD physical GI square on the same Gauss-law source xU+yW_pU. The previously proved LO two-context minor gives a positive two-row coefficient frame; MF/MK original Q_GI/N_H floor transports without changing any posterior. At selected true contexts the constant physical unit U itself satisfies (Q_GI/N_H)/(10 E_b²) ≤ L_D(R_U)²+L_Dprime(R_U)²; U is p-independent. No context- or H-uniform positivity asserted. |
| **[OF #5790](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalKrylovZeroSelectorSignedDensityFloorV5_OF.lean)** | Actual all-finite-depth right-Krylov zero-selector at scale n has true physical source exactly U for every nonnegative fine coupling beta(n+1), by GX. Therefore the same selected-context physical U floor is transferred exactly into the true signed receiver representation of that genuine right-Krylov coefficient source. Fixed frozen beta(n)>0; selected contexts and Q_GI/N_H coefficient may vary in scale/volume. |
| **[OG #5791](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalZeroSelectorAllDepthSameContextGIFrameV5_OG.lean)** | The genuine HF modal GI detector on each actual zero-selector coefficient is EXACTLY the same OD signed p0−pπ receiver functional on the unmodified physical U at fixed n; its output is identical across any pair of depths r,s. More strongly, for each fixed n with frozen beta(n)>0 and given actual links and initial boundary data, ONE pair of genuine interacting-Wilson contexts z,zprime can be chosen **before and independently of ALL r**, carrying the same positive original Q_GI/N_H coefficient in a two-row modal-square floor for every finite r. Arbitrary coefficient-source injectivity and cross-scale endpoint compatibility remain OPEN. |

| **[OH #5793](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalOneRowAllDepthModalRankOpenV5_OH.lean)** | One of OG's TWO genuine original signed GI receiver rows can be selected ONCE at a fixed scale n and genuine Wilson context; its physical zero-selector detector squared value is at least HALF the actual (Q_GI/N_H)/(10 E_b²) floor for EVERY finite Krylov depth r. That **same real scalar HF modal map** has exact coefficient kernel finrank r; at each r there is a positive-radius detected coefficient ball around a0_r. For r>0 the rank-r coefficient kernel is not asserted to synthesize a nonzero physical source. No all-source rank assumption or volume-uniform floor. |

| **[OI #5794](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovModalKernelSplitV5_OI.lean)** | For the real original HF modal GI receiver row, define a coefficient remainder `k_r(a) = a - t_r(a) a0_r`, `t_r(a) = Φ_r(a)/Φ_r(a0_r)` using OH's **proved nonzero** denominator. OI proves `Φ_r(k_r(a))=0`, exact coefficient split, and the original HJ physical Hilbert source identity `S_{n,r}(a)=S_{n,r}(k_r(a))+t_r(a)U`. It also proves, by the original HF/OD signed GI equality, that the true two-posterior FF receiver of `S_{n,r}(k_r(a))` vanishes at the SAME selected real link/context, for any a and every finite r. This is a ONE-context null, not a global invisible nonzero physical source claim. |

**Remaining obstruction after verified OD–OI source decomposition.** OH proves an actual original Wilson GI row with nonzero zero selector, quantitative half-floor, and kernel finrank r at ALL finite depths. OI constructs an explicit real decomposition in the ACTUAL right-Krylov coefficient and Gauss-law Hilbert source spaces; the residual source is annihilated by this one true interacting-posterior receiver. **It is not proved to be nonzero, nor invisible under all physical GI links and contexts**. The next substantive gate is to compare the physical synthesis image of these explicit one-row kernel remainders against the whole HJ continuous GI detector kernel, and prove actual higher-mode receiver information rather than assume rank. No H-uniform U0, cross-scale endpoint compatibility, all-coefficient positive-fine injectivity, H1-C3 or continuum gap follows.

Moreover, `M\succ0` for each finite point set does **not** provide a uniform lower bound on `λ_min(M)`, nor `inf_H Q_GI(H)/N_H>0`. OC's interpolation inverse may deteriorate with point geometry and H. These are separate, open quantitative gates.

## 6. Distinct earlier finite-volume results

- The original Wilson Haar-reference `A_W` and normalized physical Dirichlet `D₁₂` have distinct finite-volume Riesz/Loewner/restricted-spectrum results: [#5440](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5440), [#5472](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5472), [#5485](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5485).
- [#5514, ES–ET](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5514): the actual color count `L_c(H)=4(H+1)^3` and an H-dependent **relative** operator coefficient obstruction, not an absolute continuum-gap no-go.
- [#5574, GI–GL](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574): original two-interacting-posterior signed physical response lower certificate with *the genuine `Q_post`* in its denominator. Never substitute `Q_GI` for this different quantity.
- [#5601–#5639, HI–IR](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5639): actual physical signed-source detectors, physical invisible subspace `I_phys=S(ker Φ)` and restricted visible quotient. Full signed-source positivity is conditional on eliminating this invisible sector. The zero-fine/all-depth and zero-depth/all-nonnegative-fine boundary cases are proved [#5621](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5621).
- [#5661–#5665, JO–JS](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5665): genuine temporal-Wilson posterior contrast detection, original physical receiver covariance remainder and a conditional receiver-span obstruction. They remain useful **separate** theorems; the once-open *spatial* nonzero-witness gate was subsequently closed by LM rather than by silently assuming receiver-span membership.

## 7. Explicitly OPEN — the actual continuum proof obligations

1. **Uniform authentic signed-source information.** Even though a witness with `Q_GI>0` exists at each finite H, **no** positive uniform lower bound for `Q_GI/N_H` across H/spacing/scales and physically compatible contexts is proved. `E_b` and the coupling schedule also require control.
2. **Full physical source coverage and endpoint transport.** Neither a p-dependent two-source Gram nor its stable inverse proves the required source separation for **arbitrary positive fine coupling and every Krylov depth**. The zero-invisible-sector condition and the transfer of actual local source estimates to the **same genuine endpoint physical source family** are open.
3. **Spatial/scale summability.** Genuine interacting-Wilson receiver covariance and spatial tails must have appropriate localization and summable, volume-compatible constants; no Dobrushin substitute or independent-Haar conditional model may be silently introduced.
4. **H1-C1/C2/C3 strong limit**, including genuine coarse/fine compatibility and a single natural-time physical operator; physical-time semigroup, OS/Wightman reconstruction and full nontrivial continuum **4D Yang–Mills mass gap** are subsequent, separate open gates.

No single fixed-volume rank/Gram witness, positive finite-lattice spectral band, or `sorry`-free theorem resolves those continuum obligations. See the precise **[ROADMAP](ROADMAP.md)**.

## 8. Reproducing source and auditing proof integrity

Work from the **verified theorem-bearing OI checkpoint**, not default `main` or an unrelated docs-only SHA:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach e43726d7d3ec770c2fed93cfb0d1559359d6d701
cat lean-toolchain
# Optional when a compatible pinned cache is available:
lake exe cache get
# Dependency-aware build of the exact latest theorem-bearing leaf:
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalKrylovModalKernelSplitV5_OI
# Full repository build is a separate, more expensive check:
# lake build
```

The OI file has six public `#print axioms` reports in exact-head CI #39731413087, with no `sorryAx`. Five depend on standard `propext`, `Classical.choice`, `Quot.sound` only; the all-depth fixed-context existence theorem inherits five previously documented finite-lattice `native_decide` dependencies. No new unproved axiom was added. Docs-only changes are not new proofs.

For a future theorem: inspect current canonical SHA, the **complete Lean file and its physical prerequisites**, the exact changed-source-head CI and public axioms; fix errors/warnings in changed files, verify the independent MCP CI completion receipt, then merge and re-observe the new canonical SHA. The PR Lean Fast Check workflow is path-filtered to Lean sources, configuration, and scripts; a README/ROADMAP-only PR does **not** trigger the Lean workflow. Review Markdown and source links directly instead of rebuilding thousands of unchanged theorem modules.
