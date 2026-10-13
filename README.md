# MGAP4D — four-dimensional Yang–Mills formalization

Lean 4 / mathlib research by **Hidetoshi Itakura** on the original finite-volume Wilson lattice theory and the outstanding four-dimensional Yang–Mills existence and mass-gap problem.

**Checkpoint — 2026-10-13 JST: latest theorem-bearing [PR #5509 (P4-Q2-EQ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5509) MERGED at `6012204e90116fdef200a5212531ed9a4f23b483`; exact tested source HEAD `fcc314ebf60526aeb6919eff165b6a6e4a70fb8d`, [CI #38343835952](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38343835952) SUCCESS **9686/9686**, Changed Lean job `115120597354`, MCP receipt `115121787658` SUCCESS; 6/6 axioms, changed Lean errors/warnings 0, `sorryAx` absent. EP [#5508](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5508) already proved separate genuine selected Wilson Haar references bounded by true interacting physical selected color residuals. EQ now proves `QW(f_e) ≤ (12/L_{c(e)}(H))*E12_phys(f_e)` on the SAME SU(2) physical Wilson gauge-invariant witness and any `κ*E12_phys(f_e) ≤ QW(f_e)` has `κ ≤ 12/L_{c(e)}(H)`. Distinct original AW vs true physical D12 laws remain distinct. Neither growth of the actual color cardinality with H nor an H-/spacing-uniform or continuum Yang–Mills mass gap is proved.**

> **Scope.** Original Wilson Haar Riesz `AW`: actual full-physical-joint-`L²` finite-volume quadratic coercivity (DV), genuine Loewner/restriction (DW), bounded inverse and real spectral band `[κ_R,12]` (DX). **DY #5478 Lean-proves the original physical DQ/DF finite-volume witness coefficient; DZ #5480 restores the EXACT factor 12 lost when going from the original normalized Haar average to its truly UNNORMALIZED twelve-color sum, improving the SAME physical coefficient across full-L², Loewner and anti-Lipschitz bounds**. **EA #5482 proves the sharp universal nonnegative six-color-link averaging coefficient. EB #5484 applies the actual maximum six-color cardinality to the original Wilson Haar fiber reference; EC #5485 proves the new SAME physical Wilson m,M coefficient throughout the original unnormalized Wilson Riesz whole joint L² and restricted Loewner/anti-Lipschitz estimates.** This diagnoses why pure nonnegative link-count comparisons cannot remove inverse color multiplicity; the constrained real Wilson Haar residuals could admit stronger correlations, which remain unproved. Separate normalized physical `D12` and independent pair-Haar coordinate projections are never identified. **ED #5487 proves on the GENUINE spatial SU(N) gauge-configuration carrier that a one-boundary one-link real observable is invariant under all local vertex gauges iff constant; but the TWO-boundary relative link transforms by conjugation and an explicit SU(2) relative Wilson-energy class observable is gauge-invariant and pointwise nonconstant (values 0 and 2). These new ED results are pointwise, not a new original Wilson/pair-Haar L² color-block or spectral-gap estimate.** **EE–EG now add the actual bounded-continuous, simultaneously gauge-invariant SU(2) relative-link Wilson energy in DISTINCT original physical Wilson and independent pair-Haar joint L² spaces (EE), its exact two-coordinate independent-Haar support (EF), and the strictly positive finite-volume original Wilson normalized Haar reference floor controlling the two selected independent-Haar coordinate defects (EG). This does not equate the two measures or their conditional expectations.** **EH #5493 now establishes strictly positive LEFT and RIGHT selected independent pair-Haar CR projection defects for the actual bounded gauge-invariant SU(2) relative-link energy using exact normalized SU(2) Haar means and full support. EI #5494 carries these strictly positive defects through EG/EB's genuine finite-volume Wilson link-mass floor, proving strictly positive ORIGINAL Wilson normalized Haar-reference, literal unnormalized REAL Haar-reference and physical joint L² Riesz quadratic on this SAME actual gauge-invariant observable. No Wilson conditional expectation is identified with pair-Haar CR.** **EJ #5496 adds the exact original Wilson-weighted off-target resampling zero and EK #5498 proves both individual selected original Wilson Haar reference energies strictly positive with the true shared finite-H mass witness.** **EL #5500 reconstructs the exactly normalized true original Wilson 12-color and physical Riesz energies from the two strictly positive selected link Haar references, with true color cardinality and no Wilson conditional expectation identification.** **EM #5502 separately proves strict positivity of BOTH selected interacting original Wilson conditional physical color-block residuals, with equality of AZ's and EE's physical joint L² representatives.** **EN #5504 closes off-selected interacting physical Wilson color fixedness and exact physical D12 two-color support.** **EO #5506 proves finite-H same-witness genuine Wilson AW/D12 bilateral comparison.** **EP #5508 proves each selected mass-weighted original Haar link reference is bounded by its OWN interacting physical color defect.** **EQ #5509 sharpens the actual SU(2) witness upper to `QW(f_e) ≤ (12/L_{c(e)}(H))*E12_phys(f_e)` and provides a necessary bound on any relative coefficient.** **No spatial-volume/spacing-uniform physical coefficient, Yang–Mills continuum theory or positive continuum mass gap is claimed.**

See the updated [ROADMAP.md](ROADMAP.md) for the theorem-status matrix, independent Krylov/adjacent-scale obligations, and the next proof order.

## 1. Authority and reproducible environment

| Item | Verified value |
| --- | --- |
| Repository | [itakura-hidetoshi/4d-mass-gap](https://github.com/itakura-hidetoshi/4d-mass-gap) |
| **Only theorem-authoritative branch** | `formal/real-hilbert-uniform-coercive-strong-limit` |
| **Latest theorem-bearing merge** | [#5509 (EQ)](https://github.com/itakura-hidetoshi/4d-mass-gap/pull/5509), `6012204e90116fdef200a5212531ed9a4f23b483` |
| PR #5509 exact tested source HEAD | `fcc314ebf60526aeb6919eff165b6a6e4a70fb8d` |
| Lean pin | `leanprover/lean4:v4.30.0-rc2` |
| mathlib pin | `5450b53e5ddc75d46418fabb605edbf36bd0beb6` |
| Exact source-head CI | [#38343835952](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38343835952) — **SUCCESS** |
| Changed Lean / MCP completion jobs | `115120597354` / `115121787658`, both **SUCCESS** |
| Build and diagnostics | **9686/9686**, EQ six `#print axioms`, changed Lean warnings/errors **0**, inherited lattice `native_decide` and standard Lean axioms only, no `sorryAx`/new axiom/admit. |

**The GitHub default `main` is not the theorem authority.** Reobserve the fresh exact HEAD of the branch above and inspect the actual Lean theorem declarations before trusting this document, a PR title, or a historical conversation. A subsequent documentation-only merge advances the branch HEAD **without changing the #5509 theorem-bearing checkpoint**.

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

## 3. Original Wilson Riesz through EC; ED–EQ actual SU(2) physical witness

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



**EA #5482: exact SHARPNESS of the six-color averaging step, NOT a physical gap no-go.** Write `E_H` for the genuine periodic-even spatial-link carrier and `E_c` for its six actual nonempty color classes. EA constructs a genuine six-color sigma equivalence with `E_H` and, for each actual color, a single-real-link nonnegative spike. It proves the exact **iff**:

```text
(forall g : E_H -> ENNReal,
   kappa * (sum_e g(e)) <= sum_color [1/card(E_c) * sum_{e in E_c} g(e)])
iff
(forall c : Fin 6, kappa <= (card E_c)^(-1)).
```

Lean declarations `p4Q2EA_actualColorAverages_lower_coefficient_iff` and `p4Q2EA_actualColorAverage_bound_of_color_card` are theorem-bearing in the actual spatial link geometry. Thus **no improvement beyond the reciprocal of the largest actual color-cardinality is possible using an inequality for *all arbitrary nonnegative per-link weights***. The color-average coefficient is at best `1/max_c card(E_c)`. **The special set of physically realizable Wilson Haar-fiber defects is NOT proved to contain those spikes.** EA does not assert failure of an actual Wilson `AW` spectral gap or of the separate normalized physical `D12` gap. For stronger physical bounds, prove an *original-law* covariance, color-block refresh, localization or signed cancellation identity. In particular, link-cardinality growth must not be confused with a genuine physical-time Hamiltonian or its continuum spectrum.

**EB #5484 / EC #5485: sharp color-cardinality bound carried to the ORIGINAL Wilson operator.** Define the actual finite six-color maximum
`L_max(H) := max_{c : Fin 6} Fintype.card (p4Q2BA_ColorLinks H c)` (proved positive and ≤ the actual spatial-link count). EA's iff proves that `1/L_max(H)`, rather than the older DQ `1/|E_H|`, is the sharp universally justified color-average coefficient for arbitrary nonnegative ACTUAL spatial-link weights. EB proves the exact genuine original normalized physical Wilson Haar-reference lower bound

```text
a_EB(H,beta,m) = m * exp(-32*beta) / (12 * L_max(H)).
```

EC combines EB with DZ's actual 12-fold UNNORMALIZED original Wilson reference normalization and the unchanged true physical m>0 and M≥0 witnesses from DG/CP and CD/DF:

```text
kappa_EC(H,beta,m,M) =
  12 * min(1, m * exp(-32*beta) / (12 * L_max(H) * (M+1))).
```

This is the explanatory real formula for the exact Lean `ENNReal`/real definition. EC explicitly proves `kappa_DZ(H,beta,m,M) ≤ kappa_EC(H,beta,m,M)` for the SAME m,M, the true original Wilson normalized Haar-reference/variance bound, its exact original UNNORMALIZED conversion, and `kappa_EC * ‖x-P_const x‖² ≤ Q_original(x)` on the **entire** actual physical joint real L². It additionally proves the original Wilson Riesz `ContinuousLinearMap` centered Loewner bound and the original Wilson constant-orthogonal restriction's `AntilipschitzWith` estimate with the SAME coefficient. New source: `OriginalSharpMaxColorWilsonHaarFloor.lean` (EB) and `OriginalWilsonRieszSharpMaxColorFullL2.lean` (EC).

**Precise limitation:** the improvement is finite-volume, not volume-uniform. The maximum actual color size `L_max(H)` still grows with spatial volume, and both genuine original Wilson compact density lower floor `m(H,N,beta)` and variance comparison upper bound `M(H,N,beta)` remain H-dependent. No positive-beta commutation of distinct physical Wilson color projections, gauge-invariant single-link witness, original signed fine/frozen Krylov Gram uniformity, spacing-scaled semigroup, OS Hamiltonian or continuum mass gap is thereby established.

**ED #5487: genuine original SU(N) local gauge orbit, rather than arbitrary link weights.** On the ACTUAL periodic-even spatial slice of side length `2(H+1)≥2`, each physical link has distinct endpoints. A vertex gauge transformation supported at its source can send that link to **any** prescribed SU(N) value while acting on the genuine original background configuration. Thus `p4Q2ED_oneBoundary_singleLink_gaugeInvariant_iff_constant` and `p4Q2ED_pair_oneBoundarySingleLink_gaugeInvariant_iff_constant` rigorously force **any pointwise function of only ONE raw spatial link on ONE boundary** to be constant if invariant under all original local gauges. This refines EA's interpretation: its **arbitrary nonnegative single-link weight spike is not automatically an admissible nonconstant one-boundary gauge-invariant Wilson observable**.

For two original adjacent spatial boundaries `(A,B)`, however, the TRUE relative link `R_e = (A e)⁻¹ * (B e)` transforms by `R_e ↦ γ(target(e))*R_e*γ(target(e))⁻¹`. Every SU(N) conjugation-invariant real class function `phi` therefore supplies a simultaneously gauge-invariant pointwise TWO-boundary observable `phi(R_e)`, without identifying the two original Haar coordinates. Moreover ED uses the **existing actual SU(2) Wilson-energy and central negative-identity theorems** to establish a concrete such observable taking **0 at identity-relative configurations and 2 at negative-identity-relative configurations**. Lean declarations `p4Q2ED_SU2_relativeWilsonEnergy_gaugeInvariant`, `p4Q2ED_SU2_relativeWilsonEnergy_zero_two`, and `p4Q2ED_SU2_relativeWilsonEnergy_gaugeInvariant_nonconstant` close the pointwise nonconstant example.

**Proof boundary:** ED does **not** claim that these two-boundary observables realize EA's ONE-coordinate spike in the original Wilson or independent pair-Haar `L²` defects, nor that actual physical Wilson color conditional projections commute. No physical H-/spacing-uniform gap, fine/frozen signed Krylov Gram, cross-scale transport, or continuum Hamiltonian follows. EE–EN have subsequently closed this concrete SU(2) observable's separate Haar-reference and interacting physical energy support; uniformity and continuum remain open.

### EE–EI: genuinely gauge-invariant SU(2) relative link, exact two-coordinate support, strictly positive original Wilson energy

**EE [PR #5489] — CLOSED:** The actual original spatial pair carrier supports a BOUNDED CONTINUOUS and simultaneously gauge-invariant two-boundary Wilson-energy observable, (F_e(A,B)=E_W((A_e)^{-1}B_e)), with explicit configurations giving pointwise values 0 and 2. EE defines the actual original Wilson–Perron physical joint-`L²` class via the certified bounded core AND, separately, the true independent pair-Haar joint-`L²` class of the same representative. The separate almost-everywhere representative identities are proved under their correct measures. The true original Wilson Riesz quadratic equals the LITERAL original unnormalized twelve-color Haar-reference core energy for that concrete physical observable. Pointwise nonconstancy is not asserted to imply nonzero Hilbert-`L²` class without an additional support theorem.

**EF [PR #5490] — CLOSED:** In the real independent pair-Haar joint `Lp ℝ 2`, the original CR orthogonal projection `P_i` fixes EE's `f_e` for EVERY joint coordinate other than the genuine `Sum.inl e` and `Sum.inr e`. EF proves invariance under explicit updates of the actual joint coordinate measurable equivalence, then equality of the literal Haar one-coordinate integral, and invokes DA's *actual pair-Haar* conditional-expectation identification. In Lean:
```text
i != Sum.inl(e), i != Sum.inr(e) ==> P_i(f_e) = f_e
                                     ||f_e - P_i(f_e)||^2 = 0.
```
There is no assertion that interacting physical Wilson conditional projections commute or fix this observable.

**EG [PR #5491] — CLOSED:** The independent pair-Haar energy on ALL actual left/right spatial coordinates reduces to its TWO selected CR defect terms **exactly**, not as an inequality:
```text
sum_{i : Sum Link Link} ofReal(||f_e-P_i f_e||^2)
 = ofReal(||f_e-P_(inl e) f_e||^2)
   + ofReal(||f_e-P_(inr e) f_e||^2).
```
Instantiating **EB's genuine original Wilson physical Haar fiber-mass witness `m>0`** at this SAME gauge-invariant bounded continuous SU(2) pair observable proves, with the actual `ENNReal` normalization,
```text
a_EB(H,beta,m) *
   (ofReal(||f_e-P_(inl e) f_e||^2)
     + ofReal(||f_e-P_(inr e) f_e||^2))
 <= E_Haar,12^original Wilson(F_e).
```
Here `a_EB = m * exp(-32 beta)/(12 * L_max(H))` is the explanatory finite-volume coefficient and the RIGHT-HAND side is the *normalized original physical Wilson Haar reference*, **not the separate physical D12 operator or its conditional residual sum**. The pair-Haar `P_i` on the LEFT is explicitly a different operator from Wilson conditional projection.


**EH [PR #5493] — CLOSED:** For the ACTUAL finite-product independent pair-Haar real joint `L²`, the chosen left/right SU(2) relative-link Wilson-energy CR projections have *exactly the same constant representative*
```text
P_(inl e) f_e =_ae HaarMean_SU2(E_W)
P_(inr e) f_e =_ae HaarMean_SU2(E_W).
```
The proof uses real SU(2) Haar translation invariance, Wilson-energy inversion symmetry, the verified DA Haar-coordinate projection interface, open-set positivity of the true pair-Haar measure, and the explicit gauge-invariant continuous observable taking 0 and 2. Thus both selected coordinate residuals are **STRICTLY POSITIVE**:
```text
0 < ||f_e - P_(inl e) f_e||²
0 < ||f_e - P_(inr e) f_e||².
```
No physical interacting-Wilson conditional projection is substituted for the genuine independent pair-Haar `P_i`.

**EI [PR #5494] — CLOSED:** Combining EH's genuine positive selected independent-Haar residuals with EG's **actual original Wilson Haar-reference lower bound** and EB's theorem-generated finite-H `m(H,2,beta)>0`, Lean proves that the normalized physical Wilson mass-weighted twelve-color **Haar REFERENCE** of the SAME actual gauge-invariant SU(2) relative-link observable is strictly positive, for any `beta≥0` at each finite `H`. Then BD's original bounded-core finiteness and exact unnormalized 12-color sum give a strictly positive **REAL unnormalized original Wilson Haar reference**. Finally BP/EE's literal exact original bounded-core/full-physical-joint-`L²` identity transports the result without changing laws:
```text
0 < Q_W(physicalWilsonJointL2(F_e)).
```
New exact theorem identifiers: `p4Q2EI_SU2_originalWilsonNormalizedHaarReference_pos`, `p4Q2EI_SU2_originalWilsonUnnormalizedHaarReferenceReal_pos`, `p4Q2EI_SU2_originalWilsonFullJointRieszQuadratic_pos`. This is a true **single gauge-invariant finite-volume physical original Wilson Riesz strict-energy witness**, not an H-/spacing-uniform lower gap or a continuum theorem.

**After EQ #5509:** EL original Haar two-link support and EN genuine interacting physical D12 two-color support are separate CLOSED exact identities, EO original AW/D12 finite-H bilateral with genuine EC coefficient is CLOSED, EP proves original selected Haar-link ≤ true physical color residual for each side, and EQ proves actual color-cardinality-sensitive upper and relative comparison coefficient restriction. ER growth of actual physical color cardinality as H varies remains OPEN, separately from H-/spacing-uniform signed Krylov, C1/C2/C3 and H2/H3/H4.

**EJ [PR #5496] — CLOSED:** for the SAME genuine gauge-invariant two-boundary SU(2) relative-link Wilson-energy BCF, EF's true pointwise off-target coordinate invariance now gives exact zero of the **actual original Wilson–Perron density weighted** squared-difference integrand whenever the re-sampled spatial left/right joint coordinate differs from both selected copies of the link. EJ proves the literal normalized compact SU(2) Haar inner fiber integral also vanishes for every original pair configuration. The physical density is the real original continuous positive joint Wilson–Perron weight; this is **not** a conditional expectation under the interacting Wilson law. EH/EI still prove strict positivity at selected coordinates and of the total actual original physical reference/Riesz energy. The original BB/BC per-color reference was subsequently reconstructed exactly by EL #5500; physical color-block covariance, finite-H Wilson–Perron ratio control and signed fine/frozen Gram remain distinct next steps. No spatial-volume/spacing-uniform or continuum mass gap is claimed.

**EK [PR #5498] — CLOSED.** On the exact original Wilson-Perron physical joint law, `p4Q2EK_SU2_selectedOriginalWilsonLinkReference_lower_witness` uses DG's SAME strictly positive finite-volume fiber mass witness and DO's exact separate unswapped left/right Haar mass-floor-to-pair-Haar-CR-defect equalities. EH's strictly positive selected SU(2) defects then give `p4Q2EK_SU2_bothSelectedOriginalWilsonLinkReferences_pos`: BOTH literal ORIGINAL Wilson left and right **individual link Haar reference energies** are strictly positive for the same bounded, gauge-invariant relative-link witness. This advances EI from strictly positive total original reference to strictly positive selected terms individually. EJ only proves off-target Wilson-weighted literal resampling squared differences vanish; it does not yet show the original AZ/BB Haar **variance reference** is identically zero at those off-target links. **EL #5500 now proves** the exact off-target original AZ/BB Haar variance vanishing and precise two-link BB/BC twelve-color sum with correct multiplicities. Physical interacting conditional expectations, signed Krylov, H-/spacing-uniform gap and continuum remain distinct/open.

**EL [PR #5500] — CLOSED.** For the SAME genuine gauge-invariant SU(2) relative-link Wilson-energy observable, the exact original right-link split reconstruction (DK/CJ) transports EF's pointwise off-target update invariance to a constant Haar fiber section at every physical outer context. Consequently the literal original SU(2) Haar **evariance is exactly zero**, and its actual Wilson-Perron mass-weighted AZ right-link reference is zero for every link other than the selected right copy. Original boundary-swap invariance (Wilson-energy inversion symmetry) gives the corresponding genuine BB left-link reference zero. Lean proves both complete original left/right spatial-link sums localize to their own selected links. More strongly, `p4Q2EL_SU2_originalWilsonTwelveColorSum_eq_twoSelected` and `p4Q2EL_SU2_originalWilsonNormalizedReference_eq_twoSelected` reconstruct the exact original 12-color Haar reference from precisely these two selected positive Wilson reference energies with the ACTUAL selected six-color link cardinality `L_{c(e)}(H)` and normalization `1/12`. `p4Q2EL_SU2_originalWilsonUnnormalizedReferenceReal_eq_twoSelected` and `p4Q2EL_SU2_originalWilsonPhysicalRieszQuadratic_eq_twoSelected` transport the SAME identity into the literal unnormalized REAL reference and actual physical joint-`L²` Riesz quadratic; no `AW=D12` claim is made. EK proves each selected contribution strictly positive. Exact source SHA `6cdb32095acff8b1b3fc24cf67d2a0ac2a93329f` passed CI #38312807952 (9681/9681, changed file errors/warnings 0); #print axioms has standard Lean axioms and inherited hypercubic `native_decide` dependencies but no `sorryAx` or new axiom. **Historical next EM (CLOSED at #5502; physical support completed at #5504):** establish physically genuine interacting Wilson color-block conditional-expectation locality/comparison for the same gauge-invariant witness; separately improve H-dependent m/M and signed fine/frozen Krylov Gram without asserting spatial-volume or continuum uniformity.

**EM [PR #5502] — CLOSED in the selected physical color-residual strict-positivity scope.** The genuine bounded SU(2) relative-link gauge-invariant observable is represented by the same vector in AZ's original bounded concrete Wilson joint-L² and EE's original physical Wilson joint-L² (`p4Q2EM_SU2_originalAZJointL2_eq_EE`, Wilson-a.e., not pair Haar). EK's separately strict positive original physical Wilson left/right one-link Haar REFERENCES, the existing AZ/BB original-reference-to-physical-one-link residual comparisons, and sigma-algebra-inclusion monotonicity to the corresponding true physical Wilson six-color conditional-expectation blocks imply `p4Q2EM_SU2_bothSelectedPhysicalWilsonColorDefects_pos`. BOTH selected right/left original Wilson interacting 12-color conditional residual squares are strictly positive for the SAME actual SU(2) witness. Neither AW=D12 nor positive-beta commutation is asserted. **Historical next EN (CLOSED at #5504):** prove every off-selected-color genuine interacting physical Wilson conditional projection fixes this witness via retained-color sigma-algebra measurability; then exact original physical D12 twelve-color energy support and quantitative comparison, separately from EL's already-closed original Haar reference two-link decomposition. Uniform signed fine/frozen Krylov Gram and 4D continuum mass gap remain open.

**EN [PR #5504] — CLOSED:** on the SAME original gauge-invariant SU(2) relative-link Wilson physical joint-L² vector `f_e`, the five actual theorems `p4Q2EN_SU2_offSelectedPhysicalRightColor_fixed`, `p4Q2EN_SU2_offSelectedPhysicalLeftColor_fixed`, `p4Q2EN_SU2_originalPhysicalTwelveColorSum_eq_selectedTwo`, `p4Q2EN_SU2_originalPhysicalD12_eq_selectedTwo` and `p4Q2EN_SU2_originalPhysicalD12_pos` establish: for all six-colors `c ≠ c(e)`, the genuine interacting physical Wilson right/left conditional-expectation projections fix `f_e`; the original true physical twelve-color squared residual sum has exactly the two selected terms; and `E12_phys(f_e) = (1/12)*(||f_e-P^W_(R,c(e))f_e||²+||f_e-P^W_(L,c(e))f_e||²)>0`. The proof uses actual retained-sigma measurable structure, physical `lpMeas` membership, `condExpL2` orthogonal fixedness, and EM's separately strict positive selected residuals. There is no substitution by independent pair-Haar CR and no identity `AW=D12`. Exact Lean source: `OriginalRelativeWilsonSU2PhysicalOffColorD12Support.lean` (full common prefix), 336 lines; exact tested source `1f07489bdec7e40e2b78d63a3618e39c9c3dfd94`, CI #38323859362 SUCCESS (9683/9683), changed Lean errors/warnings 0, five checked `#print axioms` without `sorryAx`. **Historical EO goal subsequently CLOSED at #5506:** compare this witness's distinct AW Haar reference and interacting D12 energies using original AZ/BB/BC one-direction estimates with exact selected-color cardinality, mass factors and normalizations.

**EO [PR #5506] — CLOSED, same-genuine-Wilson SU(2) witness bilateral AW/D12 comparison.** For the **same** original Wilson physical joint-`L²` gauge-invariant SU(2) relative-link witness `f_e`, six checked Lean theorems show `κ_EC(H,beta,m,M) * E12_phys(f_e) ≤ QW(f_e) ≤ 12 * E12_phys(f_e)` with the actual typed EC coefficient for some true Wilson `m>0`, `M≥0`, and `κ_EC>0`. EN identifies the upper expression `12*E12_phys(f_e)` exactly with the TWO strictly positive selected interacting right/left color conditional residual squares, while EL independently identifies `QW(f_e)` with the actual two selected original Wilson Haar references divided by the TRUE selected-color link cardinality `L_{c(e)}(H)` (ENNReal normalization and `toReal`). The same law is retained: original Haar-reference Riesz `AW`, interacting physical normalized conditional `D12`, and independent pair-Haar are NOT identified. The six new declarations are `p4Q2EO_SU2_originalRiesz_le_twoSelectedPhysicalDefects`, `p4Q2EO_SU2_physicalD12_le_originalRiesz_positiveCoefficient`, `p4Q2EO_SU2_originalRiesz_physicalD12_selectedBilateral`, `p4Q2EO_SU2_physicalD12_le_originalRiesz_explicitWilsonMass`, `p4Q2EO_SU2_explicitWilsonMass_selectedPhysicalBilateral`, `p4Q2EO_SU2_exactOriginalHaarAndInteractingD12_twoSupport`. Exact tested source `dc5507931e27b8b296b7b90d9e3ae5ebf9f738e8`; [CI #38338446499](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38338446499) SUCCESS 9684/9684, Changed Lean job `115103769852` and MCP receipt `115104852566` SUCCESS, changed-file errors/warnings 0, six `#print axioms` without `sorryAx` (standard Lean axioms/inherited lattice `native_decide` only); theorem-bearing squash SHA `67e0f6874d8dfc1a02067ca3353f89bbca23a8bf`. **Historical next EP, CLOSED at #5508:** derive explicit genuinely interacting two-color physical defect versus selected-link mass-weighted Haar-reference inequalities with all factors preserved, then tackle original physical H-/spacing-uniform signed Krylov Gram. This is NOT a proof of uniform-in-H gap, continuum YM, or C1/C2/C3/H2/H3/H4.

**EP [PR #5508] — CLOSED, individually certified TRUE interacting physical Wilson color comparisons.** The actual original SU(2) gauge-invariant relative-link physical joint-`L²` witness satisfies the two distinct exact EL-original-Haar/EN-physical-D12 energy formulas. New `p4Q2EP_SU2_bothSelectedOriginalHaarRefs_le_physicalColorDefects` separately proves the literal ORIGINAL mass-weighted right/left Wilson link Haar reference `≤ ENNReal.ofReal` of its OWN true interacting Wilson right/left selected-six-color conditional squared residual, by the actual AZ/BB reference-to-link residual bound plus retained-sigma inclusion. Both selected interacting residuals and their two-color sum are positive; `p4Q2EP_SU2_selectedHaarReal_physicalTwoColor_bilateral` and the dimensionless ratio bound `κ_EC/12 ≤ QW/(R²+L²) ≤ 1` retain exactly the true selected color-cardinality and `m>0,M≥0` EC witnesses. Five Lean theorem declarations in `OriginalRelativeWilsonSU2SelectedHaarPhysicalColorRatio.lean`, theorem merge `df262256799bba06b9ccad515c4d314ba833a4fb`, exact source `23aaaf132255f13e26ac5fb67ea268c23f78cbdc`, CI [#38342734762](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38342734762) SUCCESS 9685/9685; Changed Lean `115117143776`, MCP receipt `115118463090` SUCCESS; 5/5 `#print axioms` no `sorryAx`, changed file warning/error 0. This is finite-H and distinct from independent pair-Haar CR.

**EQ [PR #5509] — CLOSED, stronger actual selected-color cardinality upper comparison and NECESSARY coefficient constraint.** EP's *individual genuine-original-Wilson* Haar-link ≤ interacting-physical-selected-color residual inequalities, EL's exact original Wilson selected-two-link `ENNReal` Haar sum with inverse physical `L_{c(e)}(H)`, and EN's true normalized two-selected-color D12 energy imply on this SAME SU(2) gauge-invariant original Wilson physical joint `L²` class `QW(f_e) ≤ (12/L_{c(e)}(H)) * E12_phys(f_e)`. Actual Wilson right/left Haar references are shown finite **before** using pinned `ENNReal.toReal_add`; the color count is proved positive and no arbitrary nonnegative-weight spike or pair-Haar-substituted conditional is used. Because `E12_phys(f_e)>0` by EM/EN, **any real** relative comparison coefficient `κ*E12_phys(f_e) ≤ QW(f_e)` must satisfy `κ ≤ 12/L_{c(e)}(H)`; the genuine EC coefficient `κ_EC>0` shares this upper bound, and the selected ratio is sharpened to `κ_EC/12 ≤ QW/(R²+L²) ≤ 1/L_{c(e)}(H)`. This is a **relative AW-versus-D12 witness-level finite-H** restriction: it neither disproves an absolute physical D12 gap nor proves growth of `L_c(H)` as H varies, any continuum limit, or a Yang–Mills mass gap. Six public Lean theorems in `OriginalRelativeWilsonSU2PhysicalColorCardinalityUpper.lean`, merge `6012204e90116fdef200a5212531ed9a4f23b483`, exact source `fcc314ebf60526aeb6919eff165b6a6e4a70fb8d`, CI [#38343835952](https://github.com/itakura-hidetoshi/4d-mass-gap/actions/runs/38343835952) SUCCESS 9686/9686, Changed Lean `115120597354` and MCP receipt `115121787658` SUCCESS, 6/6 `#print axioms` no `sorryAx`, changed file warnings/errors 0. **Next ER:** prove a genuine geometric growth formula/lower bound for `L_c(H)` (on the actual selected-color link carrier), and then formalize the precise relative-uniform comparison obstruction IF that growth theorem is established. H-/spacing-uniform signed fine/frozen Krylov Gram, C1/C2/C3 and H2/H3/H4 remain OPEN.




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
| **P4-Q2, quantitative full-`L²` / color averaging** | **#5468–#5485 CLOSED in distinct scopes**: genuine normalized physical D12 (DS–DU), original AW (DV–DZ), EA sharp arbitrary-link-weight iff, EB actual max-color original Wilson reference floor, and **EC same-witness original AW full joint L², Loewner/anti-Lipschitz with kappa_EC ≥ kappa_DZ**. | Original physical H-/spacing-uniformity, signed fine/frozen Gram and continuum reconstruction OPEN. |
| **P4-Q2-ED–EQ: genuine original Wilson SU(2) gauge-invariant witness** | ED–EI genuine gauge observable/positive reference; EJ–EL exact original selected Haar two-link support; EM–EN true interacting selected physical color strict positivity/exact D12 two-color support; EO #5506 finite-H AW/D12 bilateral; **EP #5508** individual selected original Haar link ≤ its own true interacting Wilson conditional color residual; **EQ #5509** `QW ≤ (12/L_c(H))*E12` and any relative κ≤12/L_c(H) on the same physical witness. | ER actual color-cardinality growth theorem, uniform signed Krylov/cross-scale physicality and continuum OPEN. |

The #5326 `W × M` signed-Krylov link-budget and the newer AW/D12 finite-volume spectral gap are **different mathematical problems**. A finite-volume positive coefficient for AW or D12 does not close the volume-uniform fine/frozen Krylov Gram, original signed Schur row estimates, or cross-scale reconstruction.

## 6. Live frontier and limitations

The live frontier after EQ #5509 is ER proving an exact physical color-carrier cardinality formula or growth lower bound for `L_c(H)`, and only THEN drawing the logically justified relative AW/D12 uniform-comparison obstruction along the genuine SU(2) witness. This relative comparison must not be confused with an absolute AW or D12 gap, a signed fine/frozen Krylov Gram estimate or a continuum mass gap. Genuine H-/spacing-uniform Wilson mass/variance and signed Krylov, C1 common marginal, C2 vector-wise reconstruction, C3 summable beta trajectory, H2 physical time, H3 OS Hamiltonian and H4 continuum Yang–Mills are all OPEN.

Do not treat positive constants separately available at each H as a common constant. The DV proof uses a finite-volume coefficient from an actual Wilson Haar fiber-mass floor and link cardinality; no bound uniform in H is proved. Existing small-beta estimates `κ12 ≥ 1/2304`, transfer gap `≥ 1/3072`, `q0=3071/3072` apply only within their verified contexts; they are **not** a nontrivial continuum time evolution.

Prior no-go/limits remain relevant: positive-coupling H1-D5 whole-operator compatibility; the specific fixed-`s>8` Dobrushin scaling certificate (#5207); and old uncorrected sup-width majorants (#5217). They do **not** refute all continuum routes. Avoid reconstructing the failed Dobrushin architecture as the default path.

## 7. Reading and reproducing the current theorem

The latest theorem-bearing Lean target lives at:

```text
MGAP4D/MathlibAnalytic/PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PhysicalColorCardinalityUpper.lean
```

On the **fresh authoritative branch** with the pinned toolchain/manifest:

```bash
lake build MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2PhysicalColorCardinalityUpper
```

Read in dependency order: DQ `OriginalTwelveColorGlobalHilbertFloor` → DC `GlobalMeanPoincare` → DF `OriginalPhysicalVarianceSandwich` → DR `OriginalWilsonVarianceTwelveColorCoercivity` → CL `OriginalBoundedCoreKernelExactFrontier` → BW/BX `OriginalFullJointL2ContinuousBilinear` / `OriginalFullJointL2Quadratic` → **DV** `OriginalFullJointHaarRieszCoercivity` → **DW** `OriginalWilsonRieszOrthogonalSpectrum` → **DX** `OriginalWilsonRieszSpectralBandAndIsUnit` → **DY** `OriginalWilsonRieszExplicitFiniteVolumeCertificate` → **DZ** `OriginalWilsonRieszExactUnnormalizedTwelveFactor` → **EA** `OriginalColorAverageSharpnessBarrier` → **EB** `OriginalSharpMaxColorWilsonHaarFloor` → **EC** `OriginalWilsonRieszSharpMaxColorFullL2` → **ED** `OriginalGaugeInvariantLocalSupport` → **EE** `OriginalRelativeWilsonSU2BCFPhysicalL2` → **EF** `OriginalRelativeWilsonSU2PairHaarCoordinateSupport` → **EG** `OriginalRelativeWilsonSU2TwoCoordinateHaarReference` → **EH** `OriginalRelativeWilsonSU2SelectedHaarStrictDefects` → **EI** `OriginalRelativeWilsonSU2PhysicalReferenceStrictPositive` → **EJ** `OriginalRelativeWilsonSU2OffTargetPhysicalHaarFiberZero` → **EK** `OriginalRelativeWilsonSU2SelectedPhysicalLinkStrictPositive` → **EL** `OriginalRelativeWilsonSU2OffTargetWilsonVarianceTwoLinkSupport` → **EM** `OriginalRelativeWilsonSU2InteractingPhysicalColorStrictEnergy` → **EN** `OriginalRelativeWilsonSU2PhysicalOffColorD12Support` → **EO** `OriginalRelativeWilsonSU2PhysicalEnergyBilateralBridge` → **EP** `OriginalRelativeWilsonSU2SelectedHaarPhysicalColorRatio` → **EQ** `OriginalRelativeWilsonSU2PhysicalColorCardinalityUpper`. All these shorthand names share the full `PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaar` prefix and `MGAP4D/MathlibAnalytic/` directory.

For the physical D12 spectrum, follow CA `OriginalPhysicalTwelveDirichletLoewner` → DS `OriginalWilsonFullJointL2PhysicalFrameCoercivity` → DT `OriginalPhysicalTwelveDirichletOperatorGap` → DU `OriginalPhysicalTwelveDirichletOrthogonalSpectrum`.

**Audit policy:** On theorem PRs verify original physical meanings, all changed Lean files **and their dependencies**, frozen Lean/mathlib pins, exact tested PR HEAD, success of targeted Lean CI plus its matching MCP receipt, and absence of new `sorry`/`admit`/axioms. Do not report warnings as zero when CI shows otherwise. On a **documentation-only** PR, change only README/ROADMAP; it moves branch HEAD but does not constitute a new mathematical theorem.
