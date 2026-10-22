# MGAP4D — 4D Yang–Mills / genuine Wilson SU(2) Lean 4 formalization

**Original interacting Wilson theory · Gauss-law physical Hilbert space · Lean 4 + mathlib · Hidetoshi Itakura**

> **Research status, 2026-10-22 JST (OO #5806 / OP #5807 exact-head verified):** In the unchanged original interacting SU(2) Wilson/Gauss-law model, OM–ON prove a genuine nonzero two-context GI minor and full **depth-one** source/GI injectivity for small positive fine t at each finite H. **OO** proves that the actual right-Krylov depth-two sources are exactly `(U,T_t U,T_t² U)`, transports OM's nonzero first-two minor to that same three-coordinate model, and constructs a NONZERO coefficient Schur residual annihilated by both selected true GI rows. **OP** proves the two-row common coefficient kernel is exactly the Schur residual LINE and both original all-context GI and physical-source kernels are contained in this line. Actual depth-two GI injectivity is **equivalent** to a nonzero third genuine posterior GI response on the Schur source; physical synthesis injectivity is **equivalent** to its actual nonzero physical Hilbert vector. **Neither nonzero condition is proved**. Arbitrary positive fine, volume-uniform U0, cross-scale endpoint, strong limit and continuum Yang–Mills mass gap remain OPEN.

**日本語要約：** 元の相互作用Wilson二posterior・Gauss-law物理Hilbert源・Perron半密度・異なるfine/frozen couplingを維持。OM #5803・ON #5804で有限体積・小正fineにおける真正二文脈minor非零と深さ1全実係数源の単射性を証明済み。**OO #5806**は元の右Krylov深さ2 `(U,T_tU,T_t²U)` を真正物理源に同定し、先頭2列minorの非零実在と真正二行GIで消える**非零係数**Schur残差を構成。**OP #5807**はその二行共通核を厳密に残差の一次元直線と証明し、全文脈GI核と真正物理源核がその直線に含まれることを示した。深さ2の全文脈GI単射性は**第三の真正Wilson GI文脈による残差検出**、物理源単射性は**残差の真正Gauss-law Hilbert像の非零性**とそれぞれ同値。ただし後者二つの非零性は未証明。次はOQ。任意正fine・任意深さ・体積一様U0・同一endpoint・強極限・連続体質量ギャップはOPEN。

**[Acceptance gates and next proofs → ROADMAP.md](ROADMAP.md)**

## 1. Theorem authority, pinned environment, and verified checkpoint

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Last verified theorem-bearing merge checkpoint (OP)** | [`a53295e837d60778959349cbf880fa6064f882de`](https://github.com/itakura-hidetoshi/4d-mass-gap/commit/a53295e837d60778959349cbf880fa6064f882de) |
| Latest verified theorem PR at this checkpoint | [#5807 — P4-Q2-OP](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5807) MERGED; [#5806 — OO](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5806) MERGED |
| Exact **tested source** SHA (distinct from squash SHA) | `13a0f59989e1366cecc6407f6848de390037613e` (OP); `e98d877a3c75245211e02f75e67e61ebdeb76cc3` (OO). Squash theorem SHA: `a53295e837d60778959349cbf880fa6064f882de` (OP), `375cd6826b997b6de923f032e33c25e37584b4ca` (OO). |
| [OP exact-head CI #39763001799](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39763001799) / [OO #39757133108](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/39757133108) | Both SUCCESS at exact source HEAD. OP **10877/10877**, 9/9 public `#print axioms`, changed warnings/errors 0/0, receipt SUCCESS, `sorryAx` none (8 standard-only, 1 inherited native_decide). OO **10876/10876**, 13/13, 0/0, receipt SUCCESS, `sorryAx` none (12 standard-only, 1 inherited native_decide). No new unproved axiom. |
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

## 5. Original Wilson Gaussian and genuine depth-two kernel obstruction: NT–OP

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
| **[OJ #5796](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalCrossContextPhysicalResidualMinorV5_OJ.lean)** | For *two actual* original interacting-Wilson HF modal GI detector rows `Phi_0=Phi(e,z)` and `Phi_1=Phi(e',z')`, the genuine cross-minor `M_01(a)=Phi_0(a0)Phi_1(a)-Phi_0(a)Phi_1(a0)` equals `Phi_0(a0)Phi_1(k_r(a))` and, using the original OD signed FF physical fiber, `Phi_0(a0)L_{D_1}(R_{S(k_r(a))})`. Given OH's **proved nonzero** anchor, all genuine link/context minors vanish **iff** the explicit OI residual lies in HJ's entire continuous GI detector kernel. Furthermore `ker S <= ker Phi_all <= ker Phi_0`; a **nonzero actual minor, if established**, would force a nonzero detectable Gauss-law physical residual. Any OH anchor-square floor controls the normalized U-direction coefficient; **at the historical OJ checkpoint the nonzero minor was not yet established; OM and ON subsequently close its depth-one small-positive-fine case**. |
| **[OK #5799](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFineEigenlineAllDepthCrossMinorObstructionV5_OK.lean)** | On the ORIGINAL normalized fine SU(2) Wilson physical transfer (at beta(n+1)), **if** the actual unit U is an eigenvector `T_fine U=cU`, all genuine right-Krylov modes are `c^j U` and every HJ physical source is `(Σ a_j c^j) U` for every finite depth. The original HF signed detector factors through this true one-dimensional physical source; therefore every OJ genuine two-context minor vanishes. Using OH's independently proved original frozen-beta nonzero anchor, at fixed n and frozen beta(n)>0 the all-depth equality `ker S_r = ker Phi_all,r` follows **in this physical eigenline branch only**. Conversely any truly nonzero minor forces `r>0`, `beta(n+1)>0` and `T_fine U` NOT to lie in the U eigenline. At actual fine beta=0 and r=0 the minors vanish unconditionally. Non-eigenline or a nonzero positive-fine minor has NOT been established. |
| **[OL #5801](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalWilsonSmallPositiveFineUnitNonEigenlineV5_OL.lean)** | IX gives the **actual original** SU(2) Wilson one-slab Haar-row difference derivative at fine beta=0 as half the *genuine spatial plaquette action difference*. The explicit IY identity and SU(2) central-twist boundaries satisfy W(B0)=0 and W(B1)>=2, so the derivative is >=1 while both row values equal 1 at beta=0. Mathlib calculus rigorously yields a positive volume-dependent interval `(0,delta_H)` on which `F_t(B0)>F_t(B1)`. IV transfers this literal pointwise nonconstancy to **physical non-eigenline `T_t U ∉ ℝU` for ALL t in that interval**, using the unmodified normalized fine Wilson transfer, Haar L² Gauss-law source and full Haar support. Under separate frozen beta(n)>0, IS/IU produce a NONZERO actual depth-one Krylov physical pivot with ZERO original GI response at one genuinely chosen context. **At OL's checkpoint, nonzero cross-context OJ minor/global visibility and arbitrary positive fine remain OPEN.** |
| **[OM #5803](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFineKrylovTwoContextMinorV5_OM.lean)** | **Actual nonzero original two-context minor** of `(U,T_tU)`: LM supplies authentic frozen spatial Wilson witness; JI provides the exact positive-fine derivative; OM proves equality with OJ's true zero/first right-Krylov HF modal GI cross-minor and detects the SAME nonzero physical depth-one pivot at a second genuine GI context. At each finite H and frozen `b>0`, both contexts are chosen before `t`; a fixed positive window `(0,δ_H)` works. No assumed rank or surrogate receiver. |
| **[ON #5804](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSmallFineDepthOneGIPhysicalSourceInjectiveV5_ON.lean)** | From OM's genuine **nonzero 2×2 minor**, proves for **every** real depth-one coefficient pair `(a₀,a₁)`: both actual HJ all-context GI detector and genuine physical Gauss-law source synthesis have trivial kernel. Equivalently `U` and `T_tU` are independent in the actual physical Hilbert source space throughout OM's small-positive-fine interval. No statement for `T_t²U`, all positive fine or uniform quantitative bounds. |
| **[OO #5806](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoKrylovSchurResidualV5_OO.lean)** | True depth-two coefficient selectors synthesize **exactly** `U,T_tU,T_t²U` in the original physical Gauss-law Hilbert space, and their HF modal evaluations match the same genuine two-Wilson-posterior GI gaps. OM's nonzero leading 2×2 minor persists at genuine depth two. An explicit **nonzero coefficient** Schur residual `R₂` is killed by the first two true GI rows; its synthesized physical source and third original signed GI response are computed exactly, but **not proved nonzero**. |
| **[OP #5807](MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoExactGIKernelV5_OP.lean)** | For the actual OO two GI rows with their proved nonzero leading minor, the **entire common coefficient kernel equals `ℝ·R₂`**. Actual `ker S₂ ⊆ ker Φ_all,2 ⊆ ℝ·R₂`. Moreover physical synthesis is injective **iff `S₂(R₂)≠0`**, and the full continuous genuine Wilson GI detector is injective **iff some third genuine link/context evaluates `R₂` nontrivially**. These are exact equivalences, **not an unconditional third-row or depth-two injectivity proof**. |

**Remaining obstruction after verified OD–OP.** The original physical depth-two question has now been reduced to ONE explicitly constructed, genuinely synthesized Schur residual `R₂`. OO proves the source is built from `(U,T_tU,T_t²U)`, the leading genuine GI minor remains nonzero, and a **nonzero coefficient** is invisible to the first two selected original GI rows. OP identifies the precise two-row kernel and bounds the all-context detector kernel and physical synthesis kernel inside `ℝ·R₂`. **A nonzero physical source `S₂(R₂)` does not by itself imply that any third original GI receiver sees it**, since global receiver completeness on that source is still open. The following two obstructions must therefore remain distinct: (i) prove `S₂(R₂)≠0` directly from the actual normalized Wilson transfer, e.g. nonzero third physical mode/physical Gram or higher fine derivatives; (ii) prove `∃(e'',z'') M₂(e'',z'')(R₂)≠0` using the original two interacting posteriors/FF receiver. No arbitrary-positive-fine, H-uniform coercivity, common endpoint or continuum mass gap follows.

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

Work from the **verified theorem-bearing OP checkpoint**, not default `main` or a documentation-only merge:

```bash
git fetch origin formal/real-hilbert-uniform-coercive-strong-limit
git switch --detach a53295e837d60778959349cbf880fa6064f882de
cat lean-toolchain
# Optional when a compatible pinned cache is available:
lake exe cache get
# Dependency-aware build of the exact latest theorem-bearing leaf:
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalDepthTwoExactGIKernelV5_OP
# Full repository build is a separate, more expensive check:
# lake build
```

The OP module has nine public `#print axioms` reports in exact-head CI #39763001799: Lean 10877/10877 SUCCESS, no `sorryAx`, changed-file warnings/errors 0/0, independent MCP receipt SUCCESS. Eight use only standard `propext`, `Classical.choice`, `Quot.sound`; one true small-fine Wilson context-existence result inherits the same five previously known finite-lattice `native_decide` axioms. OO likewise has 13/13, 10876/10876 SUCCESS. Documentation-only changes are not new mathematics.

For a future theorem: inspect current canonical SHA, the **complete Lean file and its physical prerequisites**, the exact changed-source-head CI and public axioms; fix errors/warnings in changed files, verify the independent MCP CI completion receipt, then merge and re-observe the new canonical SHA. The PR Lean Fast Check workflow is path-filtered to Lean sources, configuration, and scripts; a README/ROADMAP-only PR does **not** trigger the Lean workflow. Review Markdown and source links directly instead of rebuilding thousands of unchanged theorem modules.
