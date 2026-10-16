# MGAP4D — formalization roadmap

**Verified theorem-bearing checkpoint — 2026-10-16 JST:** [PR #5606 (P4-Q2-HM)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5606) is **squash MERGED** at `843cde8a3f64cc0909b1153b9387f4a7487fa200`, exact tested source HEAD `18c2442ce05268ec4168e11256b27ab0fe062bca`; [CI #38847368871](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38847368871) **completed SUCCESS (10699/10699)** with Changed Lean job `116800839239`, MCP completion receipt `116801895869` SUCCESS, changed Lean warnings/errors zero, and **14/14 HM `#print axioms` free of `sorryAx`**. Existing finite-hypercubic `native_decide` dependencies remain inherited. Only theorem-carrier `formal/real-hilbert-uniform-coercive-strong-limit`; default `main` is NOT authoritative.

**Verified GZ–HM theorem chain (#5592–#5606).** GZ proves the actual finite signed physical transfer equals its modal map. HF proves true real linearity of the original **two-interacting-Wilson-posterior GI expectation gap** at arbitrary fine beta>=0; HG defines the all-physical-links/all-SU(2)-pair-context common kernel `K`. HH's continuity-dependent measured mass nullity is made unconditional by HI's actual interacting Wilson density-row and genuine physical receiver continuity. HJ defines separately the genuine finite Krylov physical source synthesis `S` and continuous original GI detector `Phi`, proves `ker S<=ker Phi=K`, and a positive detector-complement stability constant. HK uses Artinian finite infimum extraction to obtain finitely many genuine physical contexts `F`, so `D_F : R^(r+1)->(F->R)` has `ker D_F=K`, and at frozen beta>0 the original GL mass vanishes iff `D_F(a)=0`. HL proves `ker S=K` iff `finrank(range S)=finrank(range D_F)`, with a strict detector rank shortfall equivalent to a nonzero physical source invisible to all original selected GI contexts. **HM #5606 now defines the LITERAL physical Haar-L² source Gram `Qsrc_(ij)=⟪v_i,v_j⟫_ℝ` and original two-Wilson-GI finite context matrix `M_(xj)=Delta_(v_j)(x)`, proves `Qsrc` positive semidefinite, `ker(Qsrc.mulVecLin)=ker S`, `Qsrc.rank=finrank(range S)`, `M.mulVecLin=D_F`, `M.rank=finrank(range D_F)`, and the necessary-and-sufficient finite matrix condition `ker S=K iff Qsrc.rank=M.rank`. A strict Gram rank excess `Qsrc.rank>M.rank` is equivalent to an actual nonzero source missed by the genuine two-posterior GI detector. **Neither source-separation nor matrix rank equality has been established unconditionally.** Do not confuse `Qsrc` with the totally distinct GL posterior-density contrast `Q_(beta,e)(z)` or with the older pair-Haar residual Gram. GU/HB one-posterior response-square is a different observable. Nothing above proves a physical source GL coercivity coefficient uniform in H,n,r/spacing, H1-C3, OS Hamiltonian, or continuum 4D Yang–Mills gap.

**Exact verified finite-volume source-family certificate (not a full frame theorem):**

```text
F_a = sum_i a_i f_i     (actual gauge-invariant physical Hilbert sources)
Q_(beta,e)(z) = ||p_(identity,e,z)-p_(pi,e,z)||²_(normalized Haar SU2) > 0
Delta_(beta,e,F_a)(z) = E_(original Wilson posterior, identity)[R_(beta,e,F_a)]
                        - E_(original Wilson posterior, pi-rotated)[R_(beta,e,F_a)]
a^T G_(beta,H) a
   >= exp(-16 beta)/(2*||T_(beta,H)||²)
         * sum_(e actual physical links) integral_(outer pair-Haar z)
             Delta_(beta,e,F_a)(z)² / Q_(beta,e)(z).
```

**Open scientific gates:** HI proves original GI boundary continuity; HJ/HK prove genuine continuous and finite detector-complement stability; HL/HM now reduce actual physical source separation to equality of the ranks of TWO LITERAL MATRICES, the true Haar-L² source Gram `Qsrc` and finite original Wilson GI context matrix `M`. This ranks criterion has NOT yet been verified to hold for actual Wilson coupling or modes. However actual physical source separation `ker S=ker Phi`, a physical-source quotient frame, the original GL-integral mass coercive coefficient and volume/lattice uniformity all remain open. Neither existence of a non-a.e.-zero `Delta` for every nonzero *actual* right-Krylov/left-three-mode combination, nor an `H,n,r`-uniform lower source frame, genuine spatial signed covariance summability, volume/coupling/spacing-uniform physical transfer normalization, or common coarse/fine physical reconstruction (C1/C2/C3) is proved. H2 physical time, H3 OS Hamiltonian, H4 Wightman/Yang–Mills continuum gap are also **OPEN**. A finite-volume positive Wilson Haar Riesz `AW`, a positive physical twelve-color `D12`, and signed physical fine/frozen Gram estimates are distinct results and must never be substituted for each other.

The **independent-Haar conditional posterior is not the physical law**: in the latest source-gap results both INNER posterior expectations are genuinely interacting Wilson laws; normalized Haar only supplies their common density reference, while pair-Haar is the distinct OUTER physical context. Preserve frozen `beta(n)` versus fine-source `beta(n+1)` and literal original link-count normalization. Historical finite-volume details are retained below with their precise limitations.

Read [README.md](README.md) for the physical definitions, scope, current inequality and exact Lean reproducibility target.

## 0. Authority, environment, and current evidence

| Field | Verified checkpoint |
| --- | --- |
| Only theorem-authoritative repository / branch | `itakura-hidetoshi/4d-mass-gap` / `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing merged PR | [#5606 (HM)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5606), merge SHA `843cde8a3f64cc0909b1153b9387f4a7487fa200` |
| Exact-tested PR #5606 source HEAD | `18c2442ce05268ec4168e11256b27ab0fe062bca` |
| Lean / mathlib | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact-source-head CI | [CI #38847368871](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38847368871) — SUCCESS |
| Changed Lean / MCP receipt jobs | `116800839239` / `116801895869`, both SUCCESS |
| Build and diagnostics | **10699/10699**, HM 14/14 `#print axioms` without `sorryAx` or new axioms; changed-file warnings/errors zero; inherited finite-lattice `native_decide` dependencies visible. |

A later **docs-only merge will move the current canonical branch HEAD** beyond the SHA shown above, but it does not alter the #5606 theorem-bearing result. Observe the branch's fresh exact HEAD for each new PR. GitHub's default `main` is not the theorem authority.

## 1. Proof status matrix

| Proof gate / lane | Actually proved in the authoritative branch | What is still open |
| --- | --- | --- |
| **P4-F1/F2/F3** | **CLOSED**, #5299–#5302: original four-crossing a.e. lift and retained-sigma fiber descent; `E_vac(beta,H)>0` for genuine finite H, `beta>0`. | Strict pointwise-in-H positivity is not an H-uniform lower bound. |
| **P4-Q1** | Fixed-H quantitative Wilson vacuum witnesses #5303–#5309; `E_vac(beta,H) ≤ |E_H| (exp(16 beta)-1)^2` in the verified regime. | Remove/prove control of `|E_H|`; no continuum control. |
| **P4-Q2 signed uncentered Krylov / EU–EY** | EU/EW original frozen Wilson signed W*M posterior beta envelopes, EV conditional K,M uniform gate, EX each-link positive-beta signed covariance, **EY #5523 exact existing real Krylov basis modes: |K_e(i,j)|≤64 beta_n²(F_i²+F_j²), full signed link covariance |G(i,j)|≤1536*(H+1)^3*beta_n²(F_i²+F_j²), Schur absolute row ≤1536*(H+1)^3*beta_n²*((r+1)*F_i²+∑F_j²)**. | Physical F_i H/r/n-uniform and original signed spatial covariance cancellation/summability still OPEN. |
| **P4-Q2 original full-`L²` Wilson forms** | #5395–#5427: original physical bounded core, dense extension and self-adjoint `AW`; #5473–#5476 add quadratic, Loewner, bilateral D12 comparison and restricted spectral band. | Uniformity and continuum OPEN. |
| **P4-Q2 qualitative full-`L²` kernel** | **CLOSED** at **#5440 / CO**: `ker(AW)=V_constants`, by real clipping/Markov contraction and a.e. constant gluing; #5441 physical mass floor. | **Not** the quantitative spectral lower estimate (supplied later by DV). Do not call CO's former CL obstruction currently open. |
| **P4-Q2 genuine pair-Haar L²** | #5442–#5455: actual CR coordinate projections, exact independent Haar factorization, commutation for these projections, Efron–Stein and global-mean Poincaré. | Never transpose pair-Haar commutation to noncommuting interacting Wilson conditional projections. |
| **P4-Q2 Wilson / Haar physical comparison** | #5456–#5467: real original Wilson / pair-Haar finite-volume variance sandwich, positive original twelve-color Haar mass floor, actual right/left fiber-to-CR defect identities and DP reference lower bound. | Constants are finite-H and may depend on beta/rank. |
| **P4-Q2 normalized→physical gap** | **#5468–#5472 CLOSED**: DQ true all-coordinate Haar floor; DR physical variance; DS full-`L²` E12 coercivity; DT D12 Loewner; DU positive real spectrum of genuine D12 restriction. | D12 is NOT AW; no H-/spacing-uniform spectrum gap. |
| **P4-Q2 original Wilson Riesz quantitative gap** | **DV #5473, DW #5475, DX #5476, DY #5478, DZ #5480 CLOSED**: original AW whole L², Loewner/D12 comparison, inverse/spectral band, explicit DQ/DF m,M witness, and **exact 12-fold normalization recovery with improved same-witness L², Loewner and anti-Lipschitz**. | Genuine H-/spacing-uniform gap and Yang–Mills continuum mass gap remain OPEN. |
| **P4-Q2-EA–EC: sharp universal link comparison → original physical Wilson Riesz** | **EA #5482, EB #5484, EC #5485 CLOSED**: EA exact universal nonnegative six-color sharpness; EB true max-color-card original Wilson normalized Haar reference; EC same original Wilson m,M coefficient improves DZ and controls whole original physical joint L², Loewner and inverse anti-Lipschitz. | Original physical H-/spacing-uniform bounds, admissible gauge-invariant localized Wilson/Haar witnesses and actual color-block comparison remain OPEN. |
| **P4-Q2-ED–ET: genuine original Wilson SU(2) witness and exact physical six-color geometry** | ED–EL real gauge-invariant relative observable and original Haar selected support; EM–EN true interacting physical D12 selected residuals; EO–EP finite-H original AW/D12 bilateral; EQ coefficient ≤12/L_c(H); ER actual growth and no positive H-uniform RELATIVE AW≥κ D12; **ES #5513 exact actual physical L_c(H)=4*(H+1)^3; ET #5514 `κ≤3/(H+1)^3` and precise max-color/selected-ratio bounds.** | Absolute operator gaps, H-/spacing-uniform signed Gram, C1/C2/C3 and H2/H3/H4 continuum remain OPEN; no absolute mass-gap no-go. |
| **P4-Q2-FC–FG: true signed Wilson link response / conditional RMS** | **FC #5530** density cancellation, **FD #5532** actual physical patch defect, **FE #5535** linkwise oscillation, **FF #5537** signed normalized response and three-way profile; **FG #5539** exact original interacting Wilson conditional M2, pair-Haar outer integrability, precise pointwise posterior-square factorization, link defect/patch/physical signed Gram Rayleigh equalities, and `beta=0` response zero. | Spatial summability of authentic `integral M2` across `24*(H+1)^3` links and H-/scale-uniform `lambda_beta^-2` are **OPEN**; no synthetic posterior or assumed localization. |
| **P4-Q2-FH–GG: genuine posterior sensitivity and physical Gram** | FH–FW keep original signed responses, true Wilson conditional RMS and Haar comparison; FZ/GA prove `Q_(beta,e,z) >= beta² exp(-32 beta) V_SU2>0`; GB–GD prove source projection `alpha` and automatic integrability; GE–GF give the positive-scale source-conditional ORIGINAL physical Gram bound and its obstruction; GG applies it to actual fine-right Krylov/left-three-mode families. | Source detection, frame uniformity, original link-profile summability, transfer and scale control remain OPEN. |
| **P4-Q2-GH–GL: true two-Wilson-posterior signed expectation gap and sharp physical Gram** | **GH #5570** pair-Haar-a.e. source detection kernel; **GI #5571** exact difference of two original Wilson posterior expectations `Delta=Q*alpha`; **GJ #5572** sharp true conditional RMS `M2>=exp(-16 beta)*Delta*alpha` and integrability; **GK #5573** finite physical patch/Gram/adjacent-scale lift, dominating coarse GA projected mass; **GL #5574** exact `Delta*alpha=Delta²/Q`, automatically integrable physical patch and arbitrary physical Gram Rayleigh bound. | Neither nonzero `Delta` for all nonzero concrete signed Krylov sources nor common physical coefficient lower bound or cross-scale continuum reconstruction has been established. |
| **P4-Q2-GM–HH: original physical transfer / two-posterior GI detection** | **GM #5576 / GN #5577** literal true Wilson transfer-fiber detector and exact GL a.e.-null criterion; **GZ #5592** actual signed Krylov transfer = modal linear map; **HA #5593 / HC #5595 / HD #5596** source-kernel inclusion and fine-beta-zero collapse / anchor-conditional classification; **HB #5594** separate single-posterior response-square kernel; **HE #5597** quantitative detector scaling; **HF #5598** real linearity of the original difference between the two interacting Wilson posterior expectations at arbitrary fine beta >=0; **HG #5599** original all-context GI joint modal kernel as a real submodule, pair-Haar full support; **HH #5600** GL mass nullity iff joint GI common kernel **under finite-mode boundary continuity**, and positivity of real physical Gram outside the common kernel under the same hypothesis. | GI boundary continuity is CLOSED by HI; still prove true nonzero GI anchor and separation `ker S = K` or identify symmetry obstructions; then derive finite-volume positive frame on physical quotient. No H-/spacing-/r-uniform frame, H1-C3, H2–H4. |
| **P4-Q2-HI: actual physical SU(2) GI full-boundary continuity, #5601 CLOSED** | Two interacting original Wilson normalized posterior fiber density rows are jointly continuous in physical right environment and SU(2) insertion; FF original physical signed (L^2) receiver is bounded-continuous; compact Haar parameter integration yields continuous two-posterior GI gap for **all** physical sources at every frozen beta >=0. Consequently **HH's finite-mode continuity hypothesis is discharged**, and at frozen beta>0, original GL mass nullity ↔ all-context HG joint GI kernel, with strict physical Gram positivity outside that kernel for nonnegative fine coupling. Exact-head 10695/10695, 9/9 axioms free of sorryAx. | **Open:** prove physical synthesis-kernel equality `ker S=K` or identify explicit SU(2) representation obstructions; positive frame on physical-source quotient, volume/lattice/scale uniformity and H1-C3 to continuum. Finite-dimensional detector quotient alone is insufficient. |
| **P4-Q2-HJ: continuous genuine two-Wilson-posterior GI detector and quotient-frame, #5603 CLOSED** | True physical finite signed synthesis `S : R^(r+1)->Phys` and full-link/full-boundary continuous GI detector `Phi : R^(r+1)->(Link->C(Pair,R))` are real linear. `ker Phi=K` (HG), `ker S<=ker Phi`, and when frozen beta>0 `GL_mass(Sa)=0 iff Phi(a)=0`. Finite-dimensional rank-nullity and mathlib injective/anti-Lipschitz produce `W` complementary to `K`, `c>0` and `||w|| <= c ||Phi(w)||_sup` for every `w in W`. Exact dichotomy: `ker S=ker Phi` OR there exists a true `S(a)!=0` with `Phi(a)=0`. 10696/10696, 10 axioms audits without sorryAx, no new warnings. | **Open:** decide the separation dichotomy by genuine SU(2) Wilson-posterior representations or exhibit an invisible physical source. The frame could be vacuous if `W=0`. The detector sup-norm frame is NOT a quantitative bound for original GL integral or finite-/continuum-volume uniform Hamiltonian mass gap. Then tackle frame/summability/C1-C3. |
| **P4-Q2-HK: finite genuine Wilson GI context kernel certificate, #5604 CLOSED** | By Artinian real finite-dimensional coefficient space + pinned mathlib `Finset.exists_inf_eq_iInf`, there exists a finite `F ⊂ Link × Pair` with `intersection_(e,z in F) ker L_(e,z)=K`. The corresponding real finite detector `D_F : R^(r+1)->(F->R)` has `ker D_F=ker Phi=K`. At frozen beta>0, `M_GL(Sa)=0 iff D_F(a)=0` for any nonnegative fine coupling. A positive finite detector anti-Lipschitz complement frame follows, and source separation reduces to `ker S=ker D_F` versus a genuine nonzero physical source invisible at all selected contexts. Exact-head 10697/10697, 8/8 axioms without sorryAx, changed warnings 0. | **Open:** nonconstructive context selection (no explicit coordinates or cardinality bound), physical source separation and SU(2) representation obstructions, a strictly positive physical-source GL integral coefficient, cross-volume summability, C1-C3, H2-H4; no continuum mass-gap theorem. |
| **P4-Q2-HL: exact actual physical-source separation iff finite original GI rank equality, #5605 CLOSED** | With HK's genuine finite SU(2) Wilson two-posterior detector `D_F`, HJ's physical synthesis `S`, and the proved `ker S<=ker D_F`, pinned mathlib rank-nullity and submodule finite-dimensionality prove `ker S=ker D_F ↔ finrank(range S)=finrank(range D_F)`. Original finite GI detector rank never exceeds actual source rank. Strict shortfall of detector rank is **equivalent** to an actual nonzero physical Haar-L² source invisible to every selected GI context. A finite set with both exact equivalences exists. Lean 10698/10698, 7/7 axioms free of sorryAx, changed warnings/errors 0. | **Open:** compute/prove the genuine physical source rank and the original Wilson posterior GI detector rank on actual mode families; decide equality or produce explicit invisible SU(2) representation sector. No bound on selected contexts or physical source frame coefficient, volume-uniform mass-gap constant, H1-C3 or continuum Yang–Mills construction. |
| **P4-Q2-HM: actual physical Haar-L² source Gram versus true two-Wilson-posterior finite GI matrix, #5606 CLOSED** | Let `v_j` be the actual physical fine right-Krylov modes, `Qsrc_ij=⟪v_i,v_j⟫_(Haar L²)`, and `M_xj=Delta_(original interacting Wilson two-posterior)(v_j)(x)` at a finite exact HK physical context certificate. `Qsrc` is positive semidefinite, `ker(Qsrc.mulVecLin)=ker S`, `Qsrc.rank=finrank(range S)`; `M.mulVecLin=D_F`, `M.rank=finrank(range D_F)`. Thus `ker S=K ↔ Qsrc.rank=M.rank` and `M.rank<=Qsrc.rank`. Strict `M.rank<Qsrc.rank` is equivalent to a true nonzero physical source invisible to every selected actual GI context. Exact-head CI 10699/10699, 14/14 axioms no sorryAx, changed warnings/errors 0. | **Open:** determine the actual two ranks or construct explicit representation-theoretic null directions from genuine interacting Wilson kernels; find/estimate concrete finite physical contexts and a positive original GL integral coefficient. `Qsrc` is NOT the GL posterior contrast Q or historic pair-Haar residual Gram. No H,n,r,spacing-uniform estimate, H1-C3, OS Hamiltonian or continuum mass gap. |
| **P4-Q2-FH–FW: genuine normalized Wilson posterior and source RMS comparison** | FH original true-RMS spatial support; FK/FL `exp(±16 beta)` true one-link posterior density/measure Haar sandwich; FM/FT original FF signed source conditional RMS squared-moment real Haar comparison; FW **equivalence** of volume-uniform spatial RMS summability and Haar comparison summability under bounded beta, **not unconditional summability**. | Actual H-/spacing-uniform `sum_e` Haar comparison response mass and transfer norm control remain OPEN. |
| **P4-Q2-FX–GA: true SU(2) normalized posterior left-sensitivity** | FZ #5561 strict original SU(2) Haar contrast variance `V_SU2>0`; GA #5562 strict quantitative all-link/right-context true posterior row difference `||p0-p1||²_Haar >= beta² exp(-32 beta) V_SU2`. | Posterior density sensitivity alone does NOT imply coercivity for every physical source. |
| **P4-Q2-GB–GD: actual physical signed-source projection** | GB #5563 exact true posterior two-row overlap `alpha_{e,f}(z)` and pointwise `M2_Wilson >= beta² exp(-48 beta) V_SU2 alpha²`; GC #5564 authentic physical link/patch energy lower bounds with explicit source projection integrability premise; GD #5565 proves its actual joint measurability and square-integrability and removes the extra premise for beta>0. | Prove source-projection nonvanishing and source-frame uniformity on the actual physical orbit; no synthetic Haar conditional laws. |
| **P4-Q2-GE–GG: physical Gram and real adjacent-scale orbit** | GE #5566 original signed physical Hilbert Gram Rayleigh lower bound for arbitrary finite source families; GF #5567 strict Gram positivity **when the true projection mass is positive**, plus necessary kernel-vanishing direction; GG #5568 extends lower certificates and explicit frame-hypothesis implications to the actual fine right-Krylov `r+1` and fine left Gram-Schmidt `3` source families with separate fine `beta(n+1)` and frozen `beta(n)`. | Establish actual signed physical source projection frame/injectivity and quantitatively uniform constants across `H,n,r`, physical transfer norm, source summability, C1/C2/C3, and continuum H2/H3/H4; all OPEN. |
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

## 3. DW–EC original Riesz; ED–ET true physical SU(2) relative Wilson energy and spatial geometry

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

**P4-Q2-EA [PR #5482] — CLOSED, in its exact universal-weight scope.** For the ACTUAL original periodic-even spatial links `E_H` and their genuine six-color partition `E_c`, the Lean theorem `p4Q2EA_actualColorAverages_lower_coefficient_iff` proves

```text
(forall g : E_H -> ENNReal,
  kappa * sum_{e in E_H} g(e)
    <= sum_{c:Fin6} (card E_c)^(-1) * sum_{e in E_c} g(e))
iff
(forall c : Fin6, kappa <= (card E_c)^(-1)).
```

Necessity is given by the **actual one-link spike** in each original nonempty spatial color; sufficiency uses the genuine DQ six-color partition and ENNReal monotonicity. `p4Q2EA_actualColorAverage_bound_of_color_card` makes the finite `K`-color-cardinality upper bound explicit. The **best possible coefficient for arbitrary nonnegative link weights** is `(max_c card E_c)^(-1)`; DQ's cruder `1/card E_H` is a universally valid, possibly weaker bound. Nothing here asserts the single-link spike is the squared defect of an original Wilson physical observable. Therefore it does NOT rule out a better *actual* Wilson `AW` gap or identify the normalized physical `D12` with `AW`.

**P4-Q2-EB [PR #5484] — CLOSED:** `L_max(H) := max_{c : Fin 6} card(p4Q2BA_ColorLinks H c)` is an ACTUAL six-color geometric cardinal, proved `0 < L_max(H) ≤ spatialLinkCard(H)`. EA's sharp iff yields the universal normalized color-average lower bound `L_max(H)^(-1)` on the genuine periodic-even link carrier. Using the unmodified DP left/right actual pair-Haar coordinate Hilbert defects and DG/CP original Wilson mass witness `m>0`, EB proves the new original Wilson normalized reference coefficient

```text
a_EB(H,beta,m) = m * exp(-32*beta)/(12 * L_max(H)).
a_DQ(H,beta,m) <= a_EB(H,beta,m).
```

**P4-Q2-EC [PR #5485] — CLOSED:** same original Wilson/independent pair-Haar variance upper comparison witness `M≥0`, same original Wilson link mass witness `m>0`, and exact unnormalized 12-color normalization DZ. EC formally defines `kappa_EC = 12 * (min (a_EB*(ENNReal.ofReal(M+1))⁻¹) 1).toReal` and proves `kappa_DZ(H,beta,m,M) ≤ kappa_EC(H,beta,m,M)` for the SAME witnesses. `p4Q2EC_originalFullJointRieszQuadratic_maxColorCoefficient` proves `kappa_EC ‖x-P_const x‖² ≤ Q_original(x)` on the ENTIRE actual physical Wilson joint real L², and the same coefficient controls the genuine original `ContinuousLinearMap` Riesz centered Loewner bound and actual constant-orthogonal inverse `AntilipschitzWith`. This does **not** establish any new physical color projection commutation or identify original `AW` with normalized physical `D12`.

**P4-Q2-ED [PR #5487] — CLOSED in exact POINTWISE gauge scope.** Using the ACTUAL spatial SU(N) lattice gauge action `(γA)_e=γ(source(e)) A_e γ(target(e))⁻¹` and the true even-side-length nonself-loop lemma, ED constructs for any `A_e` and target `u∈SU(N)` an explicit vertex gauge supported at the source that sends the selected physical link to `u`. Hence `p4Q2ED_oneBoundary_singleLink_gaugeInvariant_iff_constant` and its right-boundary pair counterpart prove one-boundary one-link gauge invariance iff the underlying group function is constant. This means EA's arbitrary positive one-link spike is **not** automatically physically admissible as a NONCONSTANT one-boundary single-link gauge-invariant observable.

The TRUE two-boundary relative link `R_e=(A_e)⁻¹ B_e` transforms under the same spatial vertex gauge by `R_e ↦ γ(target(e)) R_e γ(target(e))⁻¹`. ED proves any conjugation-invariant SU(N) class function yields a pointwise simultaneously gauge-invariant pair observable. For **actual SU(2)**, `specialUnitaryWilsonPlaquetteEnergy 2 (R_e)` is gauge invariant and explicitly takes **0** and **2** at identity and the central negative identity. It is thus pointwise NONCONSTANT on the genuine two-boundary spatial configuration carrier. These statements are NOT yet a gauge-invariant physical Wilson joint `L²` observable energy identity or a color-block spectral theorem.

**P4-Q2-EE [PR #5489] — CLOSED:** actual BOUNDED CONTINUOUS SU(2) original relative-link Wilson-energy class function (F_e(A,B)=E_W((A_e)^{-1}B_e)), simultaneous spatial gauge invariance, explicit pointwise 0/2 nonconstancy. Constructed the ACTUAL original Wilson–Perron ground-state joint real (L²) class via the physical bounded core, independently the true pair-Haar joint (L²) class, and their separate measure-correct a.e. representative identities. The original Wilson Riesz quadratic equals the literal original unnormalized Haar-reference quadratic on THIS certified core observable. Pointwise nonconstancy was not falsely promoted to nonconstant Hilbert-(L²) without a measure-support theorem.

**P4-Q2-EF [PR #5490] — CLOSED:** uses the actual joint-coordinate measurable equivalence, literal one-Haar-coordinate mean CU, and DA's genuine pair-Haar L² conditional-expectation theorem to show `P_i f_e = f_e` and `‖f_e-P_i f_e‖²=0` for every genuine joint spatial coordinate `i` distinct from both `Sum.inl e` and `Sum.inr e`. This is NOT a commutativity assumption for physical interacting Wilson conditional expectations.

**P4-Q2-EG [PR #5491] — CLOSED:** under ACTUAL independent pair-Haar real (L²) and ENNReal normalization, `p4Q2EG_SU2_allPairHaarDefects_eq_selectedTwo` proves the entire all-coordinate sum equals the sum of **exactly the two selected left/right coordinate residuals**. `p4Q2EG_SU2_originalWilsonReference_ge_selectedTwoHaarDefects` specializes EB's existing TRUE original Wilson mass witness `m>0` to the SAME bounded strongly measurable gauge-invariant SU(2) relative-link observable and gives `a_EB(H,beta,m)*(ofReal(||f_e-P_left f_e||²)+ofReal(||f_e-P_right f_e||²)) ≤ actual original Wilson normalized twelve-color Haar reference(F_e)`. Crucially the right side is **not** the normalized interacting-physical `D12`; the pair-Haar CR projections on the left are NOT original Wilson conditional expectations. At EG this strict positivity was still open; it is now **CLOSED by EH #5493**, and the corresponding genuine original physical Wilson strict-energy consequence is **CLOSED by EI #5494**.

**P4-Q2-EH [PR #5493] — CLOSED.** Both literal SU(2) selected-coordinate independent pair-Haar normalized mean operators on the physical left/right pair configuration carrier yield the SAME constant SU(2) Wilson-energy Haar average. This is via the actual left/right measurable equivalence, normalized Haar translations, Wilson-energy inversion symmetry, and the CR-to-literal-Haar mean bridge DA. Normalized finite-product SU(2) Haar measure is positive on nonempty open sets; since the genuine bounded continuous relative SU(2) observable takes 0 and 2, it cannot be Haar-a.e. constant. Therefore **both** selected CR residuals in the original independent pair-Haar real L² are strictly positive. No claim about interacting Wilson conditional projections is made.

**P4-Q2-EI [PR #5494] — CLOSED.** EG's genuine ORIGINAL Wilson normalized twelve-color Haar reference lower comparison has unchanged positive finite-volume physical Wilson fiber-mass witness `m(H,2,beta)>0`; multiply by the now EH-proved positive left+right independent pair-Haar CR residual energy of the SAME original SU(2) gauge-invariant relative observable. This yields a STRICTLY POSITIVE normalized original Wilson Haar-reference energy in `ENNReal` (typed `p4Q2EI_SU2_originalWilsonNormalizedHaarReference_pos`). BD's bounded strongly measurable original Wilson reference is finite, so the literal UNNORMALIZED twelve-color sum has strictly positive REAL `toReal` value (typed `p4Q2EI_SU2_originalWilsonUnnormalizedHaarReferenceReal_pos`). BP/EE's exact original Wilson core / full joint-L² Riesz quadratic identity transfers this strict positivity to the actual physical Wilson SU(2) ground-state joint real L² class (typed `p4Q2EI_SU2_originalWilsonFullJointRieszQuadratic_pos`). The proof does not replace AW with D12 or identify Wilson and pair-Haar probability laws.

**P4-Q2-EJ [PR #5496] — CLOSED in ACTUAL original Wilson mass-weighted off-target Haar-fiber scope.** For genuine original pair-boundary gauge-invariant SU(2) relative-link Wilson energy, EF gives pointwise off-target invariance at every independent spatial joint coordinate except the two genuine selected left/right links. EJ combines this with the original strictly positive continuous Wilson–Perron joint weight to prove the literal physically weighted squared Haar-resampling difference is 0 pointwise on all off-target coordinates; the true compact SU(2) Haar inner fiber integral of that weighted difference also equals 0. These are `p4Q2EJ_offTarget_originalWilsonMassWeightedDifference_zero` and `p4Q2EJ_offTarget_originalWilsonMassWeightedHaarFiber_zero`. Unlike EF's independent pair-Haar CR results, EJ explicitly includes the ACTUAL original Wilson density. The resulting zero is not an identification with any interacting Wilson conditional projection. **EL #5500 now closes** the original BB/BC/BD per-color energy reconstruction with the true physical split coordinates and exact left/right 12-color normalization. Compare selected contributions to true physical color block operators only through new theorems; signed fine/frozen Krylov, volume/spacing uniformity, C1/C2/C3/H2/H3/H4 and the continuum mass gap remain OPEN.

**EK [PR #5498] — CLOSED.** On the exact original Wilson-Perron physical joint law, `p4Q2EK_SU2_selectedOriginalWilsonLinkReference_lower_witness` uses DG's SAME strictly positive finite-volume fiber mass witness and DO's exact separate unswapped left/right Haar mass-floor-to-pair-Haar-CR-defect equalities. EH's strictly positive selected SU(2) defects then give `p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos`: BOTH literal ORIGINAL Wilson left and right **individual link Haar reference energies** are strictly positive for the same bounded, gauge-invariant relative-link witness. This advances EI from strictly positive total original reference to strictly positive selected terms individually. EJ only proves off-target Wilson-weighted literal resampling squared differences vanish; it does not yet show the original AZ/BB Haar **variance reference** is identically zero at those off-target links. **EL #5500 now proves** the original off-target AZ/BB Haar-variance zeros and exact selected two-link BB/BC twelve-color decomposition with correct multiplicities. Physical interacting conditional expectations, signed Krylov, H-/spacing-uniform gap and continuum remain distinct/open.

**EL [PR #5500] — CLOSED.** For the SAME genuine gauge-invariant SU(2) relative-link Wilson-energy observable, the exact original right-link split reconstruction (DK/CJ) transports EF's pointwise off-target update invariance to a constant Haar fiber section at every physical outer context. Consequently the literal original SU(2) Haar **evariance is exactly zero**, and its actual Wilson-Perron mass-weighted AZ right-link reference is zero for every link other than the selected right copy. Original boundary-swap invariance (Wilson-energy inversion symmetry) gives the corresponding genuine BB left-link reference zero. Lean proves both complete original left/right spatial-link sums localize to their own selected links. More strongly, `p4Q2EL_SU2_originalWilsonTwelveColorSum_eq_twoSelected` and `p4Q2EL_SU2_originalWilsonNormalizedReference_eq_twoSelected` reconstruct the exact original 12-color Haar reference from precisely these two selected positive Wilson reference energies with the ACTUAL selected six-color link cardinality `L_{c(e)}(H)` and normalization `1/12`. `p4Q2EL_SU2_originalWilsonUnnormalizedReferenceReal_eq_twoSelected` and `p4Q2EL_SU2_originalWilsonPhysicalRieszQuadratic_eq_twoSelected` transport the SAME identity into the literal unnormalized REAL reference and actual physical joint-`L²` Riesz quadratic; no `AW=D12` claim is made. EK proves each selected contribution strictly positive. Exact source SHA `6cdb32095acff8b1b3fc24cf67d2a0ac2a93329f` passed CI #38312807952 (9681/9681, changed file errors/warnings 0); #print axioms has standard Lean axioms and inherited hypercubic `native_decide` dependencies but no `sorryAx` or new axiom. **Historical EM frontier (since CLOSED at #5502):** establish physically genuine interacting Wilson color-block conditional-expectation locality/comparison for the same gauge-invariant witness; separately improve H-dependent m/M and signed fine/frozen Krylov Gram without asserting spatial-volume or continuum uniformity.

**EM [PR #5502] — CLOSED in the selected physical color-residual strict-positivity scope.** The genuine bounded SU(2) relative-link gauge-invariant observable is represented by the same vector in AZ's original bounded concrete Wilson joint-L² and EE's original physical Wilson joint-L² (`p4Q2EM_SU2_originalAZJointL2_eq_EE`, Wilson-a.e., not pair Haar). EK's separately strict positive original physical Wilson left/right one-link Haar REFERENCES, the existing AZ/BB original-reference-to-physical-one-link residual comparisons, and sigma-algebra-inclusion monotonicity to the corresponding true physical Wilson six-color conditional-expectation blocks imply `p4Q2EM_SU2_bothSelectedPhysicalWilsonColorDefects_pos`. BOTH selected right/left original Wilson interacting 12-color conditional residual squares are strictly positive for the SAME actual SU(2) witness. Neither AW=D12 nor positive-beta commutation is asserted. **Historical EN frontier (since CLOSED at #5504):** prove every off-selected-color genuine interacting physical Wilson conditional projection fixes this witness via retained-color sigma-algebra measurability; then exact original physical D12 twelve-color energy support and quantitative comparison, separately from EL's already-closed original Haar reference two-link decomposition. Uniform signed fine/frozen Krylov Gram and 4D continuum mass gap remain open.

**EN [PR #5504] — CLOSED:** On the SAME genuine gauge-invariant SU(2) relative-link original Wilson physical joint-`L²` observable `f_e`, the five public Lean theorems `p4Q2EN_SU2_offSelectedPhysicalRightColor_fixed`, `p4Q2EN_SU2_offSelectedPhysicalLeftColor_fixed`, `p4Q2EN_SU2_originalPhysicalTwelveColorSum_eq_selectedTwo`, `p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo`, and `p4Q2EN_SU2_originalPhysicalD12_pos` show that every off-selected right/left six-color original interacting conditional expectation fixes `f_e`; the entire physical twelve-color residual sum has exactly two selected terms, and `E12_phys(f_e)=(1/12)*(||f_e-P^W_(R,c(e))f_e||²+||f_e-P^W_(L,c(e))f_e||²)>0`. Actual retained-sigma strong measurability, Wilson `lpMeas` subspace membership and physical `condExpL2` orthogonal fixedness are used, not independent pair-Haar CR. EN differs from EL's original Haar-reference AW two-link formula. Exact tested source HEAD `1f07489bdec7e40e2b78d63a3618e39c9c3dfd94` and CI #38323859362 SUCCESS 9683/9683, changed Lean warnings/errors zero; source `OriginalRelativeWilsonSU2PhysicalOffColorD12Support.lean` (full common prefix).

**EO [PR #5506] — CLOSED, same-genuine-Wilson SU(2) witness bilateral AW/D12 comparison.** For the **same** original Wilson physical joint-`L²` gauge-invariant SU(2) relative-link witness `f_e`, six checked Lean theorems show `κ_EC(H,beta,m,M) * E12_phys(f_e) ≤ QW(f_e) ≤ 12 * E12_phys(f_e)` with the actual typed EC coefficient for some true Wilson `m>0`, `M≥0`, and `κ_EC>0`. EN identifies the upper expression `12*E12_phys(f_e)` exactly with the TWO strictly positive selected interacting right/left color conditional residual squares, while EL independently identifies `QW(f_e)` with the actual two selected original Wilson Haar references divided by the TRUE selected-color link cardinality `L_{c(e)}(H)` (ENNReal normalization and `toReal`). The same law is retained: original Haar-reference Riesz `AW`, interacting physical normalized conditional `D12`, and independent pair-Haar are NOT identified. The six new declarations are `p4Q2EO_SU2_originalRiesz_le_twoSelectedPhysicalDefects`, `p4Q2EO_SU2_physicalD12_le_originalRiesz_positiveCoefficient`, `p4Q2EO_SU2_originalRiesz_physicalD12_selectedBilateral`, `p4Q2EO_SU2_physicalD12_le_originalRiesz_explicitWilsonMass`, `p4Q2EO_SU2_explicitWilsonMass_selectedPhysicalBilateral`, `p4Q2EO_SU2_exactOriginalHaarAndInteractingD12_twoSupport`. Exact tested source `dc5507931e27b8b296b7b90d9e3ae5ebf9f738e8`; [CI #38338446499](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38338446499) SUCCESS 9684/9684, Changed Lean job `115103769852` and MCP receipt `115104852566` SUCCESS, changed-file errors/warnings 0, six `#print axioms` without `sorryAx` (standard Lean axioms/inherited lattice `native_decide` only); theorem-bearing squash SHA `67e0f6874d8dfc1a02067ca3353f89bbca23a8bf`. **Historical next EP, CLOSED at #5508:** derive explicit genuinely interacting two-color physical defect versus selected-link mass-weighted Haar-reference inequalities with all factors preserved, then tackle original physical H-/spacing-uniform signed Krylov Gram. This is NOT a proof of uniform-in-H gap, continuum YM, or C1/C2/C3/H2/H3/H4.

**EP [PR #5508] — CLOSED, individually certified TRUE interacting physical Wilson color comparisons.** The actual original SU(2) gauge-invariant relative-link physical joint-`L²` witness satisfies the two distinct exact EL-original-Haar/EN-physical-D12 energy formulas. New `p4Q2EP_SU2_bothSelectedOriginalHaarRefs_le_physicalColorDefects` separately proves the literal ORIGINAL mass-weighted right/left Wilson link Haar reference `≤ ENNReal.ofReal` of its OWN true interacting Wilson right/left selected-six-color conditional squared residual, by the actual AZ/BB reference-to-link residual bound plus retained-sigma inclusion. Both selected interacting residuals and their two-color sum are positive; `p4Q2EP_SU2_selectedHaarReal_physicalTwoColor_bilateral` and the dimensionless ratio bound `κ_EC/12 ≤ QW/(R²+L²) ≤ 1` retain exactly the true selected color-cardinality and `m>0,M≥0` EC witnesses. Five Lean theorem declarations in `OriginalRelativeWilsonSU2SelectedHaarPhysicalColorRatio.lean`, theorem merge `df262256799bba06b9ccad515c4d314ba833a4fb`, exact source `23aaaf132255f13e26ac5fb67ea268c23f78cbdc`, CI [#38342734762](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38342734762) SUCCESS 9685/9685; Changed Lean `115117143776`, MCP receipt `115118463090` SUCCESS; 5/5 `#print axioms` no `sorryAx`, changed file warning/error 0. This is finite-H and distinct from independent pair-Haar CR.

**EQ [PR #5509] — CLOSED, stronger actual selected-color cardinality upper comparison and NECESSARY coefficient constraint.** EP's *individual genuine-original-Wilson* Haar-link ≤ interacting-physical-selected-color residual inequalities, EL's exact original Wilson selected-two-link `ENNReal` Haar sum with inverse physical `L_{c(e)}(H)`, and EN's true normalized two-selected-color D12 energy imply on this SAME SU(2) gauge-invariant original Wilson physical joint `L²` class `QW(f_e) ≤ (12/L_{c(e)}(H)) * E12_phys(f_e)`. Actual Wilson right/left Haar references are shown finite **before** using pinned `ENNReal.toReal_add`; the color count is proved positive and no arbitrary nonnegative-weight spike or pair-Haar-substituted conditional is used. Because `E12_phys(f_e)>0` by EM/EN, **any real** relative comparison coefficient `κ*E12_phys(f_e) ≤ QW(f_e)` must satisfy `κ ≤ 12/L_{c(e)}(H)`; the genuine EC coefficient `κ_EC>0` shares this upper bound, and the selected ratio is sharpened to `κ_EC/12 ≤ QW/(R²+L²) ≤ 1/L_{c(e)}(H)`. This is a **relative AW-versus-D12 witness-level finite-H** restriction: it neither disproves an absolute physical D12 gap nor proves growth of `L_c(H)` as H varies, any continuum limit, or a Yang–Mills mass gap. Six public Lean theorems in `OriginalRelativeWilsonSU2PhysicalColorCardinalityUpper.lean`, merge `6012204e90116fdef200a5212531ed9a4f23b483`, exact source `fcc314ebf60526aeb6919eff165b6a6e4a70fb8d`, CI [#38343835952](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38343835952) SUCCESS 9686/9686, Changed Lean `115120597354` and MCP receipt `115121787658` SUCCESS, 6/6 `#print axioms` no `sorryAx`, changed file warnings/errors 0. **Next ER:** prove a genuine geometric growth formula/lower bound for `L_c(H)` (on the actual selected-color link carrier), and then formalize the precise relative-uniform comparison obstruction IF that growth theorem is established. H-/spacing-uniform signed fine/frozen Krylov Gram, C1/C2/C3 and H2/H3/H4 remain OPEN.

**ER [PR #5511] — CLOSED, ACTUAL original physical six-color cardinality GROWTH and no common positive relative AW/D12 coefficient.** Starting from an existing genuine spatial color-c link on the original periodic-even spatial slice of period `2(H+1)`, the Lean proof translates its original base in the SAME spatial direction by `2*k`, `k:Fin(H+1)`. The original checkerboard parity is invariant because the genuine periodic parity ring homomorphism maps even translations to zero in `ZMod 2`; distinct `2*k < 2(H+1)` have distinct ZMod residues. Consequently `p4Q2ER_evenColorEmbedding_injective`, `p4Q2ER_actualColorLinkCard_ge_halfSide` and `p4Q2ER_selectedPhysicalColorLinkCard_ge_halfSide` prove **`H+1 ≤ L_c(H)` for EVERY original physical spatial six-color**, including each SU(2) witness's selected color. Combining EQ's **genuine gauge-invariant SU(2) original Wilson physical joint-`L²`** witness-specific relative coefficient bound `κ ≤ 12/L_c(H)` and this true geometric growth proves `p4Q2ER_SU2_relativeCoefficient_mul_halfSide_le_twelve`: for `κ≥0` and `κ*E12_phys(f_e)≤QW(f_e)`, **`κ*(H+1)≤12`**. Finally `p4Q2ER_SU2_no_positive_uniformRelativeAWD12Coefficient` proves that **no positive H-uniform relative AW≥κ D12** lower coefficient is possible for all H even on the concrete SU(2) physical witness family at β=0. This is a ***relative comparison of TWO DISTINCT forms***, NOT nonexistence of an absolute AW or D12 spectral gap and NOT a physical Yang–Mills continuum/mass-gap no-go. ER itself establishes linear growth; ES #5513 subsequently proves the exact original physical cubic cardinality. Exact source `7bcda87afc979f7184cd47ca12f268ee029a975f`, [CI #38347179721](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38347179721) SUCCESS 9687/9687, Changed Lean job `115131178223` SUCCESS, MCP receipt `115132314869` SUCCESS, 5/5 `#print axioms` with standard Lean and inherited hypercubic `native_decide` only, zero `sorryAx` or new axioms, changed Lean errors/warnings zero; theorem-bearing squash SHA `798ef7db642d47dc6f1577fd936329a54348e5d7`. **Historical next ES (subsequently CLOSED by #5513):** exact spatial six-color link-cardinality formula, independent volume/spacing normalization in the true physically relevant operators, and signed fine/frozen Krylov/C1/C2/C3/H2/H3/H4, all OPEN.

**ES [PR #5513] — CLOSED, EXACT cardinality of each genuine original physical spatial six-color.** The real primary reflection-plane spatial-vertex type is equivalent to three original periodic spatial coordinates, hence has cardinality `(2*(H+1))^3`. Actual unit spatial translation interchanges the checkerboard parity fibers, and the two complementary fibers each have exactly `4*(H+1)^3` vertices. The fixed-direction genuine spatial color-c physical link carrier is typed equivalent to its actual parity fiber. Thus `p4Q2ES_actualSixColorLinkCard_exact` proves for **EVERY** original six-color `c:Fin 6`, `L_c(H) = Fintype.card (p4Q2BA_ColorLinks H c) = 4*(H+1)^3`; `p4Q2ES_selectedPhysicalColorLinkCard_exact` specializes to each concrete SU(2) relative-link witness. Four Lean public theorems in `OriginalRelativeWilsonSU2ExactSixColorCardinality.lean`, theorem-bearing merge `3492b2904cc5a4f27a16bbb6d9507707df8aebe3`, tested source HEAD `f5b14b65ab5f70ddb2e329c8b299c6f172df6249`, [exact-head CI #38349673788](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38349673788) SUCCESS (9688/9688), Changed Lean job `115138955414` and MCP receipt `115140350766` SUCCESS; changed-file warnings/errors 0, four #print axioms without sorryAx or new axioms. Genuine spatial geometry is used; no invented color carrier, relative operator identity, or continuum gap is assumed.

**ET [PR #5514] — CLOSED, EXACT CUBIC physical Wilson AW/D12 relative coefficient envelope.** From ES's `L_c(H)=4*(H+1)^3` and EQ's **same actual SU(2) gauge-invariant original Wilson physical joint-`L²` witness** `QW(f_e) ≤ [12/L_c(H)] E12_phys(f_e)`, five new Lean theorems prove: (1) `p4Q2EB_maxColorCard H = 4*(H+1)^3` on the TRUE six-color physical link carriers; (2) **every real κ satisfying `κ * E12_phys(f_e) ≤ QW(f_e)` obeys `κ ≤ 3/(H+1)^3`**, equivalently `κ*(H+1)^3 ≤ 3`; (3) the genuine fixed-H positive EC Wilson mass/variance coefficient `κ_EC(H,beta,m,M)` also obeys that exact upper bound; and (4) the positive-denominator selected-Haar/true physical-two-color ratio satisfies `κ_EC/12 ≤ QW(f_e)/(R_e+L_e) ≤ 1/[4*(H+1)^3]`. The original Wilson Haar-reference AW and genuine interacting Wilson conditional D12 remain **distinct**; this witness-specific relative coefficient restriction does NOT disprove either absolute operator's mass gap and does NOT establish a continuum Yang–Mills result. Five checked declarations in `OriginalRelativeWilsonSU2ExactCubicRelativeEnvelope.lean`; theorem-bearing merge `848ca4a763d8bb5e83cfd64f41eaede9820ff10e`, exact tested source HEAD `9b374852fe5f77e3dde2f6356f50cfa24551fab5`, [CI #38350911670](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38350911670) SUCCESS (9689/9689), Changed Lean job `115142853853`, MCP receipt `115144025946`, changed file warnings/errors **0**, five #print axioms without sorryAx/new axioms. **Historical next EU (now CLOSED in its finite-H signed Gram beta-square scope):** original-Wilson physically justified normalization or signed fine/frozen Krylov bounds; C1 actual common-marginal physicality, C2 vector-wise reconstruction, C3 summable genuine beta trajectory, H2 physical time, H3 OS Hamiltonian, H4 continuum 4D Yang–Mills remain OPEN.

**EU [PR #5516] — CLOSED, TRUE original Wilson signed fine/frozen right-Krylov cubic volume and beta-square envelope.** This is a SEPARATE proof lane from ET's original Haar-reference AW / genuinely interacting D12 relative comparison. Importing the authentic frozen Wilson ground-state half-density `W_{beta_n}`, normalized physical mean `M_{beta_n,F_a}` of the SIGNED fine beta(n+1) right-Krylov source, the positive continuous vacuum inverse, original transfer norm, and the TRUE original posterior two-copy resampling Gram identity (#5324–#5326), EU proves: **(1)** exactly `24*(H+1)^3` ORIGINAL physical spatial links using ES genuine spatial geometry (and instance-independent `Nat.card`); **(2)** nonnegative genuine source/vacuum norm factor `F_{n,r}(a)`; **(3)** the PRE-EXISTING constructed original physical Hilbert link budget exactly factors as `B_{n,r}(a) = (exp(8*beta_n)-1)*F_{n,r}(a)`; **(4)** on the ACTUAL signed uncentered fine/frozen right-Krylov Gram `G`, `aᵀ G a ≤ 12*(H+1)^3 * B_{n,r}(a)^2 ≤ 12*(H+1)^3*(exp(8*beta_n)-1)^2*F_{n,r}(a)^2` (with the 1/2 original two-copy normalization); **(5)** if frozen `beta_n=0`, the genuine budget vanishes and `aᵀGa=0` for EVERY signed coefficient vector, WITHOUT setting the distinct fine `beta_(n+1)` to zero. Seven public Lean theorem declarations in `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenCubicBetaEnvelope.lean`; [PR #5516](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5516) squash MERGED theorem-bearing SHA `b9732b42b082ea52259286ae2424ecd3c413ecf6`, exact source HEAD `df890d0ae6c3e21c0d872b962d0edbbf1c4d027c`, [CI #38355767802](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38355767802) **SUCCESS (10612 jobs)**, Changed Lean job `115158168811`, MCP completion receipt `115159353988` SUCCESS, changed Lean warnings/errors zero, all 7 `#print axioms` without `sorryAx`/new axioms. **OPEN**: H-/spacing-uniform control of `F_{n,r}(a)`, genuinely summable signed covariance/Gram rows or cancellations, C1 common physical marginal, C2 vector-wise reconstruction, C3 genuine summable beta trajectory, H2 nontrivial physical-time evolution, H3 OS Hamiltonian, H4 four-dimensional continuum Yang–Mills positive mass gap. The cubic bound is NOT itself uniform; the absolute physical D12 / original AW gaps and ET relative comparison remain distinct.

**EV [PR #5518] — CLOSED, authentic frozen Wilson signed fine/frozen small-beta estimate and CONDITIONAL uniform certification.** For genuine frozen `0≤beta_n≤1/8`, pinned mathlib gives `exp(8*beta_n)-1≤16*beta_n`; on the SAME actual original Wilson signed fine/right Krylov receiver, `aᵀG a≤3072*(H+1)^3*beta_n²*F_(n,r)(a)^2` where EU's `F` retains original half-density, inverse transfer and positive-vacuum, normalized mean and SIGNED fine beta_(n+1) source. A common Rayleigh bound `aᵀGa≤3072*K*M*∑a_j²` is derived **ONLY IF** independently certified, uniform `K,M≥0` satisfy `(H+1)^3*beta_n²≤K` and `F²≤M*∑a_j²` for every level/horizon/signed coefficient. EV DOES NOT prove those physical certificates. Five Lean theorems, merge SHA `4d36a88033132383da03b2f935cc3cd3909739e2`, source HEAD `ba2a670a6081f8c8b42408789d46a57b7396df3b`, [CI #38357988380](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38357988380) SUCCESS 10613/10613, Changed Lean `115165249298`, MCP receipt `115166618409` SUCCESS, 5/5 #print axioms without sorryAx, warnings/errors zero.

**EW [PR #5519] — CLOSED, TRUE original Wilson posterior each-link zero and projection fixedness at FROZEN beta_n=0.** From EU's exact signed fine/right Krylov Rayleigh zero and the #5324 exact ORIGINAL Wilson two-copy posterior identity `aᵀGa=(1/2)∑_e E_e(O_a)`, with `E_e=2*‖V(F_a)−Q_eV(F_a)‖²≥0` on the SAME true Wilson law, Lean proves EACH actual spatial link separately has `E_e(O_a)=0`; correspondingly every true transported frozen-Wilson right-link projector `Q_e` fixes the full signed receiver. Fine beta_(n+1) remains genuinely distinct and need NOT be zero. No pair-Haar substitute, unproved positive-beta locality or unconditional H-uniform Gram result. Two Lean theorems, merge SHA `1ebd718b4a4dfe735e563b8fd3923797e90a9be6`, tested source `9b2c3d33b62dc93e8c93c28a35af204da5d4a9eb`, [CI #38359534529](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38359534529) SUCCESS 10614/10614, Changed Lean `115170184807`, MCP receipt `115171459067` SUCCESS, changed warning/error zero, 2/2 #print axioms no sorryAx/new axioms. Next EX positive-beta original Wilson per-link signed covariance energy with physical norm factors explicit; C1/C2/C3/H2/H3/H4 all OPEN.

**EX [PR #5521] — CLOSED, positive-frozen-beta genuine original Wilson EACH-LINK signed fine/frozen covariance.** For the actual original Wilson posterior at EACH physical spatial right link e and signed fine beta_(n+1) Krylov combination a with frozen `0≤beta_n≤1/8`, four checked Lean theorems prove the TRUE posterior two-copy resampling energy `E_e(O_a) ≤ (exp(8*beta_n)-1)^2*F_(n,r)(a)^2 ≤ 256*beta_n²*F_(n,r)(a)^2`, with EU's original Wilson half-density, positive continuous vacuum inverse, normalized mean, transfer norm and signed fine source all kept inside genuine F. The exact original two-copy identity yields `‖I_e(a)‖²≤128*beta_n²*F_(n,r)(a)^2`; for ANY two SIGNED coefficient vectors a,b, Cauchy–Schwarz applied only to their true original frozen Wilson transported residuals yields `|⟪I_e(a),I_e(b)⟫|≤64*beta_n²*(F_(n,r)(a)^2+F_(n,r)(b)^2)`. No positivity of signed covariance, invented posterior or premature sum over `24*(H+1)^3` links. **These are linkwise finite-H bounds, NOT H/r/n-uniform true Wilson F norm or signed Schur row summability.** Four public Lean theorems in `OriginalSignedFineFrozenPositiveBetaLinkwiseCovariance.lean`, theorem-bearing squash merge `89eabcf38455ed55ddd8de32f0e61bea46afc707`, exact tested source `d445a9fcc20f12cb121b22711e3ce08fe1d8f56d`, [CI #38365264750](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38365264750) SUCCESS 10615/10615, Changed Lean `115188758993`, MCP receipt `115190203550` SUCCESS, 4/4 #print axioms with no sorryAx/new axiom and changed errors/warnings zero. Next EY genuine per-mode basis and signed Schur-row handoff; C1/C2/C3, H2/H3/H4 remain OPEN.

**EY [PR #5523] — CLOSED, genuine ORIGINAL Wilson signed fine/frozen mode covariance and explicit Schur-row upper.** From EX's actual original frozen-Wilson EACH-LINK residual cross-inner-product bounds for arbitrary SIGNED fine/right input combinations, EY specializes to true standard basis coefficient vectors of the EXISTING `Fin(r+1)` Krylov mode carrier and proves: **(1)** original signed basis-combination receiver/link residual equals the existing original Wilson mode-link posterior innovation (typed exact identity); **(2)** individual mode link residual squared `≤128*beta_n²*F_i²`; **(3)** each original Wilson SIGNED link covariance `|K_e(i,j)|≤64*beta_n²*(F_i²+F_j²)`; **(4)** original mode covariance `G(i,j)=∑_e K_e(i,j)` retains signs until the last triangle inequality and has `|G(i,j)|≤1536*(H+1)^3*beta_n²*(F_i²+F_j²)`; **(5)** original signed Schur ROW `∑_j|G(i,j)|≤1536*(H+1)^3*beta_n²*((r+1)*F_i²+∑_jF_j²)`. The factor `1536=24*64` uses the ACTUAL original physical spatial link count proved by EU; the mode count `r+1` is retained. **No genuine H/r/n-uniform physical norm bound, spatial signed covariance decay/cancellation, C1/C2/C3 or H2/H3/H4 continuum mass-gap theorem.** The original Wilson posterior is not replaced by independent pair-Haar, and AW/D12 relative comparison is a separate lane. Five checked theorems in `OriginalSignedFineFrozenModeCovarianceSchurEnvelope.lean`, [PR #5523](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5523) **MERGED**, theorem-bearing SHA `4ea4a6ed79b9ccfa427cb4b5b3a57175b7bd32d7`, exact-tested source `956cb7c34214d379151a7b4840b6a64c7deb2da2`, [CI #38374046001](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38374046001) SUCCESS **10616/10616**, Changed Lean job `115217832348`, MCP receipt `115219524749` SUCCESS, changed warnings/errors 0 and 5/5 `#print axioms` without `sorryAx`/new axioms. Initial CI #38366858610 failed only on a **redundant trailing `ring` after `simp` had already closed its goal** in the final Schur row proof; removed that tactic, without changing any mathematical statement. **Next EZ:** genuinely signed original Wilson Schur covariance cancellation/spatial-tail summability or physically established uniform source/vacuum norms, while keeping the present estimates as finite-H.









**Historical EL–ET true original Wilson AW vs D12 relative comparison and geometry, EU–EX authentic original frozen-Wilson signed Gram, EV conditional K,M, EW beta_n=0 link fixedness, EX positive beta link covariance, and EY #5523 original signed mode covariance/Schur ROW bounds are CLOSED in their finite-H scopes.** The uniform true physical mode norm F_i, genuine spatial signed covariance cancellation/summability, C1/C2/C3/H2/H3/H4 continuum 4D Yang–Mills remain OPEN; do not mistake a Schur upper depending on 24*(H+1)^3 and r+1 for a uniform Gram theorem.


**Still OPEN:** physical signed fine/frozen Krylov Gram uniformity; C1 common-marginal physicality, C2 vector-wise reconstruction, C3 summable genuine beta trajectory; H2 spacing-scaled nontrivial evolution, H3 OS Hamiltonian, H4 4D Yang–Mills continuum existence and positive mass gap.

## 4. Independent signed uncentered physical fine/frozen Krylov Gram — EU added

P4-Q2-DV does **not** supply the unresolved uniform signed physical Krylov Gram bound. Keep the older line active where it remains physically relevant.

**EU #5516 now proves on the SAME authentic original Wilson frozen law** `aᵀG a ≤ 12*(H+1)^3*(exp(8 beta_n)-1)^2*F_{n,r}(a)^2`, where the explicitly defined physical factor F still contains the full Wilson half-density sup norm, inverse transfer/vacuum and signed fine physical source and normalized mean. In particular frozen beta_n=0 yields Rayleigh 0 for every real signed coefficient vector, without changing fine beta_(n+1). These are finite-volume estimates, not H-/spacing-uniform signed Schur row bounds.


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

### Active after P4-Q2-GL #5574 — exact signed physical source expectation-gap square

Work at fixed original Wilson finite volume `H`, true frozen coupling `beta>0` and actual physical gauge-invariant sources. Let the original left boundaries be the identity and an explicit physical SU(2) pi rotation, and fix the SAME real physical right context `z.2` and genuine link `e`. Write

```text
d_(beta,e,z)(g) = p_(identity,e,z)(g) - p_(pi,e,z)(g)
Q_(beta,e)(z) = integral_(g ~ normalized SU2 Haar) d_(beta,e,z)(g)^2
               >= beta² exp(-32 beta) V_SU2 > 0        (FZ/GA)
Delta_(beta,e,F)(z)
  = integral R_(beta,e,F)(z,g) d[true Wilson posterior identity](g)
  - integral R_(beta,e,F)(z,g) d[true Wilson posterior pi](g)
alpha_(beta,e,F)(z) = integral R_(beta,e,F)(z,g) d_(beta,e,z)(g) dHaar(g) / Q_(beta,e)(z)
Delta = Q*alpha   (GI);   Delta*alpha = Delta²/Q   (GL).
```

The exact FG true Wilson physical source response `R` contains the complete **SIGNED** original link-update receiver, half-density factor and inverse positive continuous vacuum. Its inner posterior moments use the interacting Wilson conditional law. The original true physical residual Gram is evaluated on the signed source combination `F_a=sum_i a_i f_i`, and GL proves:

```text
0 <= Delta_(beta,e,F_a)(z)^2 / Q_(beta,e)(z)
M2_originalWilson(beta,e,F_a,z) >= exp(-16 beta)*Delta_(beta,e,F_a)(z)^2/Q_(beta,e)(z)
integral_(outer pair-Haar z) Delta_(beta,e,F_a)(z)^2/Q_(beta,e)(z) is finite,
a^T G_(beta,H) a
  >= exp(-16 beta)/(2*||T_(beta,H)||²)
       * sum_(e in original spatial links)
           integral_(outer pair-Haar z) Delta_(beta,e,F_a)(z)^2/Q_(beta,e)(z).
```

Read [GL #5574](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5574) (exact Haar density-row denominator and integrability), [GK #5573](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5573) (true physical link/patch/Gram and actual adjacent-scale Krylov lift), [GJ #5572](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5572) (sharp original conditional RMS), [GI #5571](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5571) (two actual original Wilson posterior expectations), and [GH #5570](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5570) (a.e. kernel detection). The earlier GE/GF/GG projected mass floor `beta² exp(-48 beta) V_SU2/(2||T_beta||²)` is **proved to be weaker than or equal to** the sharp GJ/GK certificate, not discarded. The genuine adjacent fine-source orbit contains `beta(n+1)` while the frozen law/Gram uses `beta(n)` at `Hn=halfExtent(n+1)`. The original three physical left modes are not replaced by an orthogonal synthetic family.

**What is closed:** existence of the **source-conditioned** real-valued finite-volume integral and its original physical Gram lower estimate, automatic measurability/integrability, strict `Q>0`, and exact zero/Gram-obstruction implications. **What is NOT closed:** a nonzero `Delta` for every nonzero physical right-Krylov source (GH/GI give a criterion, not a witness); a *uniform* positive source-detection Rayleigh frame; the true signed covariance spatial tails; uniform physical transfer normalization; and the continuum Yang–Mills spectral problem. The first is a finite-volume physical **source-selection** question, the second an H/depth/scale quantitative **frame** question; neither is implied by posterior-row sensitivity.

**Concrete immediate proof order (non-Dobrushin):**

1. **Actual source detection:** on `RightFactor(n,j)` and `LeftFactor(n,r,k)` (real, signed coefficients), compute/estimate the two interacting Wilson conditional expectations of the ACTUAL FF response. Prove or classify a nonzero a.e. `Delta_(beta(n),e,F_a)` for each physical candidate sector; characterize genuine undetected subspaces rather than imposing a fake rank hypothesis.
2. **Physical frame and conditioning:** examine the smallest eigenvalue of the true integrated `Delta(F)^2/Q` form on the authentic finite-dimensional source span, preserving all coefficient dependencies. A condition `K_(H,n,r)(F_a) >= gamma_(H,n,r)*sum_i a_i²` is an **obligation**, not a current theorem. Record any real rank deficiency explicitly.
3. **Volume/depth scaling and signed tails:** derive both the lower source-frame rate and an independently justified **upper** spatial covariance/summability bound. Do not infer a uniform upper bound from the positive lower Rayleigh estimate; monitor the actual `24*(H+1)^3` physical links and original SU(2) Wilson weight.
4. **Frozen/fine transfer compatibility:** retain distinct fine `beta(n+1)` source evolution and frozen `beta(n)` posterior/Gram. Bound the actual `||T_(beta(n),Hn)||^-2` factor and the scale dependence of `Q`, `Delta` and physical source norms. If coupling tends to zero, the GA `beta²` separation floor degenerates; the current theorems alone cannot compensate for it.
5. **C1–C3 then H2–H4:** only after genuine physicality, vector-wise coarse/fine transport and explicit summable coupling trajectory are proved may one seek nontrivial continuum natural-time semigroup, OS Hamiltonian and Wightman/Yang–Mills gap.

**Hard invariants:** never identify original interacting Wilson posterior with independent Haar conditional expectation, or `AW` with `D12` or a physical transfer generator. Treat `a.e.` equalities as `a.e.`, never pointwise by fiat. Earlier finite-H AW and physical D12 gap positivity does not imply any continuum Hamiltonian mass gap.

### Historical checkpoint P4-Q2-FG #5539: genuine conditional-response RMS and then FH frontier

For the **original** Wilson conditional posterior `nu^{Wilson}_{beta,e,z}` define `M2_{beta,e,f}(z) := integral_g R_{beta,e,f}(z,g)^2 d nu^{Wilson}_{beta,e,z}(g)`, where `R` is FF's true signed half-density/vacuum-normalized physical response. FG proves `0 <= M2`, `M2 <= ||R||_sup²`, genuine outer pair-Haar integrability, and the exact resampling square identity. The **a.e.**, not pointwise, identity `w_beta(z)*(W_beta(z)*Omega_beta(z.2)^-1)^2 = lambda_beta^-2` gives:

```text
D_e(f) = (lambda_beta^-2 / 2) * integral_z M2_{beta,e,f}(z) d muPair(z)
E_S(f) = (lambda_beta^-2 / 2) * sum_{e in S} integral_z M2_{beta,e,f}(z) d muPair(z)
a^T G a = E_ALL(sum_i a_i f_i)
```

The two inner/outer laws remain different: **Wilson conditional** inside, pair-Haar outside. No replacement by independent Haar conditional law, no finite support or spatial falloff for generic Krylov/vacuum source, no orthonormality of physical source family, and no `H`-uniform norm of the transfer operator are assumed. The authentic link number is `24*(H+1)^3`. **Historical next step after FG:** FH was to inspect the true original fine/frozen signed physical source (fine `beta(n+1)`, frozen `beta(n)`) and Wilson kernel for link-specific structure, seek directly integrable conditional-RMS tails/summability, and transmit only established scale-dependent coefficients to open C1–C3. Non-Dobrushin route; H2–H4 still OPEN.

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
| **Sharp actual six-color universal link-weight coefficient** | **`OriginalColorAverageSharpnessBarrier`** | **#5482** |
| **Optimal max-color original Wilson Haar reference floor** | **`OriginalSharpMaxColorWilsonHaarFloor`** | **#5484** |
| **Max-color coefficient through original Wilson Riesz whole L² and Loewner/inverse** | **`OriginalWilsonRieszSharpMaxColorFullL2`** | **#5485** |
| **Actual local gauge no-go for raw one-boundary link and concrete nonconstant SU(2) relative-pair Wilson energy** | **`OriginalGaugeInvariantLocalSupport`** | **#5487** |
| **Actual bounded continuous SU(2) relative Wilson physical and pair-Haar joint L²** | **`OriginalRelativeWilsonSU2BCFPhysicalL2`** | **#5489** |
| **Actual pair-Haar off-target CR coordinate projection fixed/defect-zero** | **`OriginalRelativeWilsonSU2PairHaarCoordinateSupport`** | **#5490** |
| **Exact two-coordinate pair-Haar energy and original Wilson normalized Haar-reference lower bound** | **`OriginalRelativeWilsonSU2TwoCoordinateHaarReference`** | **#5491** |
| **Strict positive selected left/right pair-Haar SU(2) CR residuals** | **`OriginalRelativeWilsonSU2SelectedHaarStrictDefects`** | **#5493** |
| **Strict original Wilson normalized/unnormalized Haar reference and physical joint-L² Riesz energy** | **`OriginalRelativeWilsonSU2PhysicalReferenceStrictPositive`** | **#5494** |
| **Actual original Wilson-Perron off-target SU(2) Haar weighted replacement difference zero** | **`OriginalRelativeWilsonSU2OffTargetPhysicalHaarFiberZero`** | **#5496** |
| **Both selected genuine original Wilson left/right one-link Haar reference energies strictly positive** | **`OriginalRelativeWilsonSU2SelectedPhysicalLinkStrictPositive`** | **#5498** |
| **Genuine original Wilson off-target AZ/BB Haar variance zero and exactly two selected physical link support: normalized 12-color, unnormalized REAL and Riesz** | **`OriginalRelativeWilsonSU2OffTargetWilsonVarianceTwoLinkSupport`** | **#5500** |
| **True interacting Wilson selected left/right physical twelve-color conditional residual strict positivity** | **`OriginalRelativeWilsonSU2InteractingPhysicalColorStrictEnergy`** | **#5502** |
| **Actual off-selected interacting Wilson physical conditional fixedness; exact positive normalized D12 two-color sum** | **`OriginalRelativeWilsonSU2PhysicalOffColorD12Support`** | **#5504** |
| **Genuine finite-H SU(2) original Haar AW versus interacting physical D12 bilateral, exact two supports and actual EC mass coefficient** | **`OriginalRelativeWilsonSU2PhysicalEnergyBilateralBridge`** | **#5506** |
| **Individual selected true original Wilson Haar right/left link references ≤ own interacting physical color squared defects; exact selected two-color bilateral ratio** | **`OriginalRelativeWilsonSU2SelectedHaarPhysicalColorRatio`** | **#5508** |
| **Selected physical six-color cardinality inverse upper `QW≤12/L_c(H)*E12` and necessary bound on any genuine relative comparison κ; sharper ratio** | **`OriginalRelativeWilsonSU2PhysicalColorCardinalityUpper`** | **#5509** |
| **ACTUAL spatial six-color growth H+1≤L_c(H), and no positive H-uniform RELATIVE AW≥κ D12 on SU(2) original Wilson witness family** | **`OriginalRelativeWilsonSU2ActualPhysicalColorGrowth`** | **#5511** |
| **EXACT original physical six-color link cardinality `L_c(H)=4*(H+1)^3` for all H,c; actual parity-fiber and spatial-vertex equivalences** | **`OriginalRelativeWilsonSU2ExactSixColorCardinality`** | **#5513** |
| **EXACT original Wilson SU(2) relative AW/D12 cubic coefficient envelope `κ≤3/(H+1)^3`; actual max-color and selected-ratio** | **`OriginalRelativeWilsonSU2ExactCubicRelativeEnvelope`** | **#5514** |
| **EU independent original Wilson signed fine/frozen Krylov physical norm beta-square Gram envelope, exact actual total spatial links, and frozen β_n=0 Rayleigh zero** | **`OriginalSignedFineFrozenCubicBetaEnvelope`** | **#5516** |
| **EV TRUE signed fine/frozen small beta squared upper and CONDITIONAL common physical K,M uniform Rayleigh gate** | **`OriginalSignedFineFrozenSmallBetaUniformGate`** | **#5518** |
| **EW TRUE original Wilson EACH spatial-link posterior energy zero and transported frozen-beta-zero projection fixedness** | **`OriginalSignedFrozenWilsonLinkwiseZero`** | **#5519** |
| **EX true ORIGINAL Wilson positive beta linkwise resampling/residual²/signed arbitrary-combination cross covariance with source F visible** | **`OriginalSignedFineFrozenPositiveBetaLinkwiseCovariance`** | **#5521** |
| **EY original signed fine/frozen Krylov BASIS-mode true Wilson link covariance and full physical spatial Schur row** | **`OriginalSignedFineFrozenModeCovarianceSchurEnvelope`** | **#5523** |
| **EZ actual original Wilson signed mode Gram Cauchy, null-row, physical trace and geometric covariance Schur** | **`OriginalSignedFineFrozenGramCauchyTraceV5_EZ`** | **#5525** |
| **FA original Wilson Gram trace Rayleigh (without Schur ℓ¹ loss), finite physical trace bound and conditional all-scale trace gate** | **`OriginalSignedFineFrozenTraceRayleighV5_FA`** | **#5527** |
| **FB genuine frozen Wilson kernel signed mean L2→BCF sup, original source norm factor and whole-source Rayleigh** | **`OriginalKernelL2SupPhysicalSourceV5_FB`** | **#5529** |
| **FC original Wilson density-cancelled link oscillation, true two-copy resampling and signed source-norm Gram WITHOUT W or Ω inverse sup factors** | **`OriginalDensityCancelledLinkEnergyV5_FC`** | **#5530** |
| **FD original Wilson all-Hilbert physical link patch defect, two-regime min-bound, input-family Gram and beta-zero fixedness** | **`OriginalPhysicalLinkLocalizedTwoRegimeV5_FD`** | **#5532** |
| **FE constructed genuine original Wilson nonuniform BCF link oscillation profile, patch sum and arbitrary physical-family Gram** | **`OriginalActualLinkOscillationProfileV5_FE`** | **#5535** |
| **FF constructed original Wilson half-density-normalized relative signed link responses, EXACT joint-moment energy and FE/FF three-way min patch/Gram** | **`OriginalSignedPhysicalRelativeLinkProfileV5_FF`** | **#5537** |
| **FG exact original Wilson conditional response mean-square, pair-Haar integrability, link/patch and signed physical Gram Rayleigh identities** | **`OriginalConditionalResponseRMSV5_FG`** | **#5539** |

| **FZ universal SU(2) temporal Wilson Haar contrast variance positive** | **`OriginalSU2TemporalWilsonContrastHaarVarianceV5_FZ`** | **#5561** |
| **GA uniformly positive true normalized Wilson two-row posterior Haar L² separation** | **`OriginalPosteriorUniformLeftHaarL2FloorV5_GA`** | **#5562** |
| **GB true signed physical source–posterior density contrast projection and conditional RMS bound** | **`OriginalSignedSourcePosteriorContrastProjectionV5_GB`** | **#5563** |
| **GC source projected mass pair-Haar link/patch energy with integrability exposed** | **`OriginalIntegratedSourcePosteriorContrastProjectionV5_GC`** | **#5564** |
| **GD automatic source projection square-integrability; unconditional physical patch lower bound** | **`OriginalSourcePosteriorProjectionAutomaticIntegrabilityV5_GD`** | **#5565** |
| **GE actual physical arbitrary signed input Gram Rayleigh and explicit frame obligation** | **`OriginalSourceProjectionGramRayleighV5_GE`** | **#5566** |
| **GF strictly positive scale and detected-source Gram criterion; zero Gram implies zero projection** | **`OriginalSourceProjectionDetectionCriterionV5_GF`** | **#5567** |
| **GG actual adjacent fine right-Krylov / left-three-mode genuine Wilson projection Rayleigh bounds** | **`OriginalActualAdjacentKrylovSourceProjectionV5_GG`** | **#5568** |
| **GH original source projected mass vanishing iff a.e. zero and Gram-null witness criterion** | **`OriginalProjectedSourceAEKernelV5_GH`** | **#5570** |
| **GI exact expectation gap of TWO original Wilson posterior conditional laws and `Delta=Q*alpha`** | **`OriginalTwoWilsonPosteriorSourceExpectationGapV5_GI`** | **#5571** |
| **GJ sharp original conditional Wilson source RMS `M2>=exp(-16beta)*Delta*alpha`, auto integrability** | **`OriginalSharpExpectationGapConditionalRMSV5_GJ`** | **#5572** |
| **GK exact original physical patch, Gram and actual adjacent fine right/left source-family sharp expectation-gap bounds** | **`OriginalSharpExpectationGapPhysicalGramV5_GK`** | **#5573** |
| **GL exact `Delta*alpha=Delta²/Q`; finite pair-Haar integrability and original physical patch/Gram lower bounds** | **`OriginalExpectationGapSquareContrastVarianceV5_GL`** | **#5574** |


Minimal latest Lean target after checking out the newly observed authoritative branch:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalExpectationGapSquareContrastVarianceV5_GL
```

**Proof-integrity process:** exact authoritative branch SHA first; exact Lean file, dependencies and physical definitions second; docs and exact-source-head CI after that. Inspect the full error context and pinned mathlib syntax, not just the highlighted line. No new `sorry`, `admit`, `axiom` or hidden synthetic physical laws. Preserve true original sum/average normalization, and explicitly report nonfatal warnings (DV had four). Use targeted changed-Lean CI and reusable pinned caches where possible; do not rebuild the entire project needlessly. For a documentation-only update, modify **only README.md and ROADMAP.md** and do not present its resulting merge SHA as a new theorem-bearing checkpoint.
