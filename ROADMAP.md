# MGAP4D — formalization roadmap

**Status: 2026-10-13 JST. Latest theorem-bearing [PR #5498 (P4-Q2-EK)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5498) MERGED at `d3d0d26baf9cecce60ace88f260f19f46a6b2d6a`; exact-source-head [CI #38308454038](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38308454038) SUCCESS (9680/9680). Both selected genuine SU(2) original Wilson-Perron left/right link Haar reference energies are now individually strictly positive. EH #5493, EI #5494 and EJ #5496 remain merged. No interacting conditional-projection identity, H-uniform or continuum mass gap follows.**

**Current theorem achievement:** DV full original Wilson Riesz quadratic coercivity, DW true Loewner and separate D12 bilateral comparison, DX boundedly invertible original orthogonal restriction with real spectrum in `[κ_R,12]`, and **DY typed original DQ/DF finite-volume mass/variance coefficient; DZ restores the literal factor 12 from normalized Haar reference to the unnormalized ORIGINAL Wilson Riesz sum with improved same-witness whole-L², Loewner and anti-Lipschitz estimates**. DU separately proves the normalized physical D12 restricted gap.

**EE–EI further achievement:** EH proves strict positivity of BOTH independent pair-Haar selected CR defects by exact Haar mean and full-support SU(2) arguments; EI proves strictly positive actual original Wilson normalized and unnormalized Haar-reference energies and the literal full physical joint-L² Riesz quadratic on this SAME SU(2) gauge-invariant observable. The coefficient remains finite-H. **EE–EG prerequisite achievements:** EE constructs the actual gauge-invariant SU(2) relative-Wilson BOUNDED CONTINUOUS observable and its separate true original Wilson and independent pair-Haar joint L² classes, plus the literal original Wilson Riesz core quadratic. EF proves pair-Haar CR projections fix it at all off-target left/right spatial coordinates. EG proves exact reduction of all such pair-Haar coordinate residual energy to the two selected left/right links, together with EB's genuine original Wilson normalized twelve-color Haar-reference lower bound for that same physical pair observable. NONE identifies physical Wilson conditional operators with pair-Haar CR projections; no H-uniform coefficient or continuum result follows. **EA–ED theorem scopes:** EA/EB/EC prove the original finite-volume color coefficient and Riesz inequalities; ED separately proves pointwise original SU(N) gauge action one-boundary one-link constancy and an explicit nonconstant two-boundary SU(2) relative Wilson-energy gauge invariant. The ED pointwise result does not extend the original Wilson spectral gap itself. **EA/EB/EC theorem scope:** EA gives the exact best universal nonnegative weight bound `kappa ≤ 1/max_c card(E_c)`. EB applies the optimal true maximum-color denominator to the ORIGINAL Wilson Haar reference (same m); EC transports its improved exact unnormalized coefficient to all original physical joint L² and the genuine Riesz Loewner/inverse stability with same m,M. This is not a common H-uniform lower bound or physical mass-gap no-go. **Main unresolved scientific target:** control the dependence of the physically relevant quantities on spatial volume `H`, coupling/scales and the actual original-Wilson fine/frozen Krylov family, then establish actual cross-scale reconstruction, nontrivial continuum physical time and a **positive continuum Yang–Mills mass gap**. No such continuum result is claimed.

Read [README.md](README.md) for definitions, exact Wilson-versus-Haar normalization, core theorem, and reproduction command.

## 0. Authority, environment, and current evidence

| Field | Verified checkpoint |
| --- | --- |
| Only theorem-authoritative repository / branch | `itakura-hidetoshi/4d-mass-gap` / `formal/real-hilbert-uniform-coercive-strong-limit` |
| Latest theorem-bearing merged PR | [#5498](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5498), merge SHA `d3d0d26baf9cecce60ace88f260f19f46a6b2d6a` |
| Exact-tested PR #5498 source HEAD | `586c96dfb37733c9afc3a2c411aaf3110bac8841` |
| Lean / mathlib | `v4.30.0-rc2` / `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact-source-head CI | [#38308454038](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38308454038), SUCCESS |
| Changed Lean / MCP receipt jobs | `115008083245` / `115009969848`, both SUCCESS |
| Build and diagnostics | **9680/9680**, EK changed-file errors/warnings 0; #print axioms for both EK theorems: propext/Classical.choice/Quot.sound only; no new axiom/sorry/admit/sorryAx. |

A later **docs-only merge will move the current canonical branch HEAD** beyond the SHA shown above, but it does not alter the #5498 theorem-bearing result. Observe the branch's fresh exact HEAD for each new PR. GitHub's default `main` is not the theorem authority.

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
| **P4-Q2-EA–EC: sharp universal link comparison → original physical Wilson Riesz** | **EA #5482, EB #5484, EC #5485 CLOSED**: EA exact universal nonnegative six-color sharpness; EB true max-color-card original Wilson normalized Haar reference; EC same original Wilson m,M coefficient improves DZ and controls whole original physical joint L², Loewner and inverse anti-Lipschitz. | Original physical H-/spacing-uniform bounds, admissible gauge-invariant localized Wilson/Haar witnesses and actual color-block comparison remain OPEN. |
| **P4-Q2-ED–EK: gauge-invariant SU(2) original Wilson local reference strict energy** | **ED–EI** bounded joint SU(2) gauge witness with strictly positive original Wilson full Riesz quadratic; **EJ #5496** actual Wilson-weighted off-target Haar replacement difference zero; **EK #5498** strictly positive selected LEFT and RIGHT literal original Wilson one-link Haar references with the SAME finite-H mass floor. | Exact original AZ/BB off-target Haar variance zero and 12-color two-support decomposition (EL), interacting color block, signed Krylov, volume uniform gap, and continuum OPEN. |
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

## 3. DW–EC original Riesz estimates; ED–EK actual gauge-invariant SU(2) strict local original Wilson energies

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

**P4-Q2-EJ [PR #5496] — CLOSED in ACTUAL original Wilson mass-weighted off-target Haar-fiber scope.** For genuine original pair-boundary gauge-invariant SU(2) relative-link Wilson energy, EF gives pointwise off-target invariance at every independent spatial joint coordinate except the two genuine selected left/right links. EJ combines this with the original strictly positive continuous Wilson–Perron joint weight to prove the literal physically weighted squared Haar-resampling difference is 0 pointwise on all off-target coordinates; the true compact SU(2) Haar inner fiber integral of that weighted difference also equals 0. These are `p4Q2EJ_offTarget_originalWilsonMassWeightedDifference_zero` and `p4Q2EJ_offTarget_originalWilsonMassWeightedHaarFiber_zero`. Unlike EF's independent pair-Haar CR results, EJ explicitly includes the ACTUAL original Wilson density. The resulting zero is not an identification with any interacting Wilson conditional projection. **Next OPEN P4-Q2-EL:** connect this exact support to the full actual original Wilson BB/BC/BD per-color energy via correct Fubini, density placement and the exact twelve-color left/right normalizations. Compare selected contributions to true physical color block operators only through new theorems; signed fine/frozen Krylov, volume/spacing uniformity, C1/C2/C3/H2/H3/H4 and the continuum mass gap remain OPEN.

**EK [PR #5498] — CLOSED.** On the exact original Wilson-Perron physical joint law, `p4Q2EK_SU2_selectedOriginalWilsonLinkReference_lower_witness` uses DG's SAME strictly positive finite-volume fiber mass witness and DO's exact separate unswapped left/right Haar mass-floor-to-pair-Haar-CR-defect equalities. EH's strictly positive selected SU(2) defects then give `p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos`: BOTH literal ORIGINAL Wilson left and right **individual link Haar reference energies** are strictly positive for the same bounded, gauge-invariant relative-link witness. This advances EI from strictly positive total original reference to strictly positive selected terms individually. EJ only proves off-target Wilson-weighted literal resampling squared differences vanish; it does not yet show the original AZ/BB Haar **variance reference** is identically zero at those off-target links. **Next OPEN EL:** prove this exact original off-target AZ/BB variance vanishing with the actual split contexts and endpoint swap, then the precise BB/BC twelve-color sum equals the two selected reference contributions with correct multiplicities. Physical interacting conditional expectations, signed Krylov, H-/spacing-uniform gap and continuum remain distinct/open.

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

Minimal latest Lean target after checking out the newly observed authoritative branch:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2SelectedPhysicalLinkStrictPositive
```

**Proof-integrity process:** exact authoritative branch SHA first; exact Lean file, dependencies and physical definitions second; docs and exact-source-head CI after that. Inspect the full error context and pinned mathlib syntax, not just the highlighted line. No new `sorry`, `admit`, `axiom` or hidden synthetic physical laws. Preserve true original sum/average normalization, and explicitly report nonfatal warnings (DV had four). Use targeted changed-Lean CI and reusable pinned caches where possible; do not rebuild the entire project needlessly. For a documentation-only update, modify **only README.md and ROADMAP.md** and do not present its resulting merge SHA as a new theorem-bearing checkpoint.
