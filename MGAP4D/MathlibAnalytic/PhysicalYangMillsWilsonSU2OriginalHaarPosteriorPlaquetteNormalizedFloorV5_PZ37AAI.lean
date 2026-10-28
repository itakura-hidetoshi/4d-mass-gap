import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPosteriorCertifiedPositiveFineRayleighV5_PZ37AAH
import MGAP4D.MathlibAnalytic.FiniteRealHilbertGramRowBesselBound
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AAI — original Haar/source-norm upper meets genuine posterior GL frame

The SAME true original Gauss-law centered physical Wilson source V_H has
its reference product-Haar-L2 norm bounded by 6 P_H (AAG/AAF), where P_H
is the number of ACTUAL spatial Wilson plaquettes, not an invented volume.
AAG/AAF cannot be imported together with the ZW/ZP branch at this pinned
HEAD because two historical modules declare the SAME local-instance name
p4Q2PZ37ZB_measurableSpace. We preserve BOTH original merged histories
and independently REPROVE the identical local-Haar centered covariance,
24-Bessel synthesis, and LO/JU physical representation in this single
compatible theorem carrier. No axiom or surrogate presentation is used.

The original TWO-interacting-posterior full-link full-pair-Haar GL Gram
(ZP/ZX/ZW) has, at each fixed H and frozen b>0, a genuine positive
two-mode coefficient-frame constant m_(H,b). In the centered direction
its true GL mass is at least m_(H,b)/4. As V_H is nonzero,

  R_(H,b)(V_H) >= m_(H,b) / (24 P_H).

The bound is a TRUE original source-normalized, posterior-dependent
Rayleigh lower bound. It in turn gives an actual finite-volume positive
fine radius via AAE, with c=m/(24 P_H) and R(F_t)>=c/2.

A UNIFORM positive fine-ZERO Rayleigh floor c would follow if one can
prove a family of original posterior two-mode Gram/frame constants
m_H >= 24 c P_H. That extensive posterior lower frame premise is
NOT proved here: it is an explicit SUFFICIENT condition, not necessary.
In particular the upper product-Haar bound is NOT used as a posterior
lower Gram bound. No uniform positive fine interval, endpoint E/F,
H1-H4, continuum mass gap, new axiom or surrogate posterior/source.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter Matrix ProbabilityTheory
open scoped ENNReal InnerProductSpace BigOperators Topology

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37AAI_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AAI_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AAI_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AAI_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AAI_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37AAI_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- ORIGINAL local Wilson plaquette with its true product-Haar mean removed.
Redefined in this import-compatible proof path; it is exactly the same
Haar-L2 function as the original ZA presentation, NOT a model replacement. -/
noncomputable def p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) :=
  ContinuousMap.toLp 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
      (p4Q2LO_originalLocalPlaquetteContinuous H p) -
    (∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A
      ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) •
      ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))

section Spatial
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "μ" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 μ ℝ
local notation "W" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "V" => p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H

noncomputable def p4Q2PZ37AAI_centeredPlaquetteContinuous (p : Plaq) : C(Cfg, ℝ) :=
  W p - (∫ A, W p A ∂μ) • (1 : C(Cfg, ℝ))

local notation "VC" => p4Q2PZ37AAI_centeredPlaquetteContinuous H

theorem p4Q2PZ37AAI_centeredPlaquette_toLp (p : Plaq) : L (VC p) = V p := by
  simp only [p4Q2PZ37AAI_centeredPlaquetteContinuous,
    p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource, map_sub, map_smul]

private theorem p4Q2PZ37AAI_toLp_inner (f g : C(Cfg, ℝ)) :
    ⟪L f, L g⟫_ℝ = ∫ A, f A * g A ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ g] with A hf hg
  rw [hf, hg]
  change (g A) * (f A) = (f A) * (g A)
  exact mul_comm _ _

private theorem p4Q2PZ37AAI_centered_integrable (p : Plaq) : Integrable (VC p) μ :=
  memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := 1) μ ℝ (VC p))

private theorem p4Q2PZ37AAI_centered_integral_zero (p : Plaq) :
    (∫ A, VC p A ∂μ) = 0 := by
  have hW : Integrable (W p) μ :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := 1) μ ℝ (W p))
  change (∫ A, W p A - (∫ B, W p B ∂μ) * 1 ∂μ) = 0
  simp only [mul_one]
  rw [integral_sub hW (integrable_const _)]
  simp

/-- True centered Wilson source has variance at most one on original Haar. -/
theorem p4Q2PZ37AAI_centeredPlaquette_norm_le_one (p : Plaq) : ‖V p‖ ≤ 1 := by
  let m : ℝ := ∫ A, W p A ∂μ
  let u := L (1 : C(Cfg, ℝ))
  let x := L (W p)
  have hu : ‖u‖ = 1 := p4Q2LR_originalHaarUnit_norm H
  have hinner : ⟪x, u⟫_ℝ = m := by
    simpa only [x, u, ContinuousMap.one_apply, mul_one, m] using
      p4Q2PZ37AAI_toLp_inner H (W p) (1 : C(Cfg, ℝ))
  have hshift : ‖x - u‖ ≤ 1 := by
    let f : C(Cfg, ℝ) := W p - 1
    have hae : ∀ᵐ A ∂μ, ‖(L f) A‖ ≤ (1 : ℝ) := by
      filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f] with A hA
      rw [hA, Real.norm_eq_abs]
      have hbounds := specialUnitaryWilsonPlaquetteEnergy_mem_Icc
        (by norm_num : 0 < (2 : ℕ))
        (periodicHypercubicEvenSpatialSlicePlaquetteHolonomy A p)
      change |W p A - 1| ≤ 1
      have hw0 : 0 ≤ W p A := hbounds.1
      have hw2 : W p A ≤ 2 := hbounds.2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have hlp := MeasureTheory.Lp.norm_le_of_ae_bound
      (f := L f) (C := (1 : ℝ)) (by norm_num) hae
    simpa [f, x, u, measureUnivNNReal, map_sub] using hlp
  have hshiftSq : ‖x - u‖ ^ 2 ≤ 1 := by
    nlinarith [norm_nonneg (x - u)]
  rw [norm_sub_sq_real, hinner, hu] at hshiftSq
  have hvSq : ‖V p‖ ^ 2 ≤ 1 := by
    change ‖x - m • u‖ ^ 2 ≤ 1
    rw [norm_sub_sq_real, real_inner_smul_right, hinner, norm_smul, hu]
    simp only [Real.norm_eq_abs, mul_one, sq_abs]
    nlinarith [sq_nonneg (m - 1)]
  nlinarith [norm_nonneg (V p)]

/-- A coordinate extension used only to demonstrate exact four-link dependence. -/
private noncomputable def p4Q2PZ37AAI_supportExtend (p : Plaq)
    (a : pz37zaSpatialPlaquetteSupport H p → Gauge) : Cfg := by
  classical
  exact fun e => if h : e ∈ pz37zaSpatialPlaquetteSupport H p then a ⟨e, h⟩ else 1

private theorem p4Q2PZ37AAI_supportExtend_continuous (p : Plaq) :
    Continuous (p4Q2PZ37AAI_supportExtend H p) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e ∈ pz37zaSpatialPlaquetteSupport H p
  · simpa [p4Q2PZ37AAI_supportExtend, he] using
      (continuous_apply (⟨e, he⟩ : pz37zaSpatialPlaquetteSupport H p))
  · simp only [p4Q2PZ37AAI_supportExtend, he, dite_false]
    exact continuous_const

private theorem p4Q2PZ37AAI_centered_support_restrict (p : Plaq) (A : Cfg) :
    VC p (p4Q2PZ37AAI_supportExtend H p (fun e => A e)) = VC p A := by
  classical
  have he (k : Fin 4) :
      pz37zaSpatialPlaquetteBoundary H p k ∈ pz37zaSpatialPlaquetteSupport H p :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have h0 :
      (p.1, p.2.1.1) ∈ pz37zaSpatialPlaquetteSupport H p := by
    simpa [pz37zaSpatialPlaquetteBoundary] using (he 0)
  have h1 :
      (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.1, p.2.1.2) ∈
        pz37zaSpatialPlaquetteSupport H p := by
    simpa [pz37zaSpatialPlaquetteBoundary] using (he 1)
  have h2 :
      (periodicHypercubicEvenSpatialSliceShift H p.1 p.2.1.2, p.2.1.1) ∈
        pz37zaSpatialPlaquetteSupport H p := by
    simpa [pz37zaSpatialPlaquetteBoundary] using (he 2)
  have h3 :
      (p.1, p.2.1.2) ∈ pz37zaSpatialPlaquetteSupport H p := by
    simpa [pz37zaSpatialPlaquetteBoundary] using (he 3)
  simp [p4Q2PZ37AAI_centeredPlaquetteContinuous,
    p4Q2LO_originalLocalPlaquetteContinuous_apply,
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
    p4Q2PZ37AAI_supportExtend, h0, h1, h2, h3]

/-- Disjoint true link supports imply orthogonality on the ACTUAL reference Haar
L2 carrier. No assertion of independence under either Wilson posterior. -/
theorem p4Q2PZ37AAI_centeredPlaquette_inner_zero_of_disjoint
    (p q : Plaq)
    (hpq : Disjoint (pz37zaSpatialPlaquetteSupport H p)
      (pz37zaSpatialPlaquetteSupport H q)) :
    ⟪V p, V q⟫_ℝ = 0 := by
  classical
  have hcoords : iIndepFun (fun (e : Link) (A : Cfg) => A e) μ := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hrestrict := iIndepFun.indepFun_finset
    (pz37zaSpatialPlaquetteSupport H p) (pz37zaSpatialPlaquetteSupport H q)
    hpq hcoords (fun e => measurable_pi_apply e)
  have hpmeas : Measurable (fun a => VC p (p4Q2PZ37AAI_supportExtend H p a)) :=
    ((VC p).continuous.comp (p4Q2PZ37AAI_supportExtend_continuous H p)).measurable
  have hqmeas : Measurable (fun a => VC q (p4Q2PZ37AAI_supportExtend H q a)) :=
    ((VC q).continuous.comp (p4Q2PZ37AAI_supportExtend_continuous H q)).measurable
  have hind : IndepFun (VC p) (VC q) μ := by
    have h := hrestrict.comp hpmeas hqmeas
    apply h.congr
    · filter_upwards with A
      exact p4Q2PZ37AAI_centered_support_restrict H p A
    · filter_upwards with A
      exact p4Q2PZ37AAI_centered_support_restrict H q A
  rw [← p4Q2PZ37AAI_centeredPlaquette_toLp H p,
    ← p4Q2PZ37AAI_centeredPlaquette_toLp H q, p4Q2PZ37AAI_toLp_inner]
  rw [hind.integral_fun_mul_eq_mul_integral
    (p4Q2PZ37AAI_centered_integrable H p).aestronglyMeasurable
    (p4Q2PZ37AAI_centered_integrable H q).aestronglyMeasurable,
    p4Q2PZ37AAI_centered_integral_zero H p, zero_mul]

/-- All absolute Gram row sums of the actual centered plaquette family are
bounded by 24, uniformly in H. Both finite incidence and Haar covariance
premises are discharged above, not assumed. -/
theorem p4Q2PZ37AAI_centeredPlaquette_gram_row_le_twentyFour (p : Plaq) :
    (∑ q : Plaq, |⟪V p, V q⟫_ℝ|) ≤ 24 := by
  classical
  have hentry (q : Plaq) : |⟪V p, V q⟫_ℝ| ≤ 1 := by
    calc
      |⟪V p, V q⟫_ℝ| ≤ ‖V p‖ * ‖V q‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul
        (p4Q2PZ37AAI_centeredPlaquette_norm_le_one H p)
        (p4Q2PZ37AAI_centeredPlaquette_norm_le_one H q) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hsum : (∑ q : Plaq, |⟪V p, V q⟫_ℝ|) =
      ∑ q ∈ pz37zaSpatialPlaquetteOverlap H p, |⟪V p, V q⟫_ℝ| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro q _hq hnot
    rw [p4Q2PZ37AAI_centeredPlaquette_inner_zero_of_disjoint H p q
      (pz37zaSpatialPlaquetteSupport_disjoint_of_not_overlap H p q hnot), abs_zero]
  rw [hsum]
  calc
    _ ≤ ∑ _q ∈ pz37zaSpatialPlaquetteOverlap H p, (1 : ℝ) :=
      Finset.sum_le_sum (fun q _ => hentry q)
    _ = ((pz37zaSpatialPlaquetteOverlap H p).card : ℝ) := by simp
    _ ≤ 24 := by exact_mod_cast pz37zaSpatialPlaquetteOverlap_card_le_twentyFour H p

end Spatial

/-- Actual original SU(2) spatial-plaquette Haar-L2 centered linear
synthesis. The common underlying configuration and Haar are original. -/
noncomputable def p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialSlicePlaquette H → ℝ) :
    Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) :=
  ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
    a p • p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p

/-- ORIGINAL full spatial-plaquette Haar Gram 24-Bessel bound, with
one genuine link-support covariance row for each actual plaquette. -/
theorem p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis_sq_le
    (H : ℕ)
    (a : PeriodicHypercubicEvenSpatialSlicePlaquette H → ℝ) :
    ‖p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H a‖^2 ≤
      24 * ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H, (a p)^2 := by
  classical
  exact finiteRealHilbert_synthesis_sq_le_gram_row_bound
    (v := p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H)
    24
    (fun p => p4Q2PZ37AAI_centeredPlaquette_gram_row_le_twentyFour H p)
    a

/-- In particular the unit-weight ORIGINAL centered Wilson
plaquette Haar sum has squared norm controlled by 24 times the
literal finite spatial-plaquette count, not a thermodynamic proxy. -/
theorem p4Q2PZ37AAI_originalCenteredHaarPlaquetteUnitSum_sq_le_card
    (H : ℕ) :
    ‖p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H
      (fun _ => (1 : ℝ))‖^2 ≤
      24 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  have h :=
    p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis_sq_le
      H (fun _ => (1 : ℝ))
  simpa using h

/-- The actual original GLOBAL Wilson action is the Finset sum
of its canonical genuine spatial plaquette energies, with no
coordinate or Wilson action replacement. -/
theorem p4Q2PZ37AAI_originalSpatialWilsonContinuous_eq_finsetSum
    (H : ℕ) :
    p4Q2JI_actualSpatialWilsonContinuous H =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        p4Q2LO_originalLocalPlaquetteContinuous H p := by
  classical
  simpa [periodicHypercubicEvenSpatialSlicePlaquetteList] using
    (p4Q2LO_originalSpatialWilsonContinuous_eq_localSum H)

/-- Exact original spatial Wilson Haar embedding is the sum of
original toLp plaquettes; continuous source embedding is real-linear. -/
theorem p4Q2PZ37AAI_originalSpatialWilsonHaar_eq_finsetSum
    (H : ℕ) :
    ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (p4Q2JI_actualSpatialWilsonContinuous H) =
      ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
        ContinuousMap.toLp 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
          (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
  rw [p4Q2PZ37AAI_originalSpatialWilsonContinuous_eq_finsetSum H]
  simp only [map_sum]

/-- Every original local Wilson continuous observable's inner
product with the ORIGINAL constant Haar-L² vacuum equals its genuine
product-Haar mean. This is a physical integral identity, not a
surrogate probability measure. -/
theorem p4Q2PZ37AAI_originalLocalPlaquetteHaar_inner_unit_eq_integral
    (H : ℕ) (p : PeriodicHypercubicEvenSpatialSlicePlaquette H) :
    inner ℝ
      (ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (p4Q2LO_originalLocalPlaquetteContinuous H p))
      (ContinuousMap.toLp 2
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) ℝ
        (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))) =
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (p4Q2LO_originalLocalPlaquetteContinuous H p),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ)
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
      (1 : C(PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2, ℝ))]
    with A hA hOne
  rw [hA, hOne]
  change (1 : ℝ) * p4Q2LO_originalLocalPlaquetteContinuous H p A =
    p4Q2LO_originalLocalPlaquetteContinuous H p A
  ring

/-- The ORIGINAL Gauss-law physical spatial-Wilson vacuum mean is
the sum of the original individual plaquette Haar means. -/
theorem p4Q2PZ37AAI_originalPhysicalWilsonMean_eq_plaquetteHaarSum
    (H : ℕ) :
    inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
      (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) =
    ∑ p : PeriodicHypercubicEvenSpatialSlicePlaquette H,
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2 := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar :=
    ContinuousMap.toLp 2 haar ℝ
  let Phys := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  have hInnerSum :
      ∀ s : Finset Plaq,
        inner ℝ (∑ p ∈ s, L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) =
        ∑ p ∈ s, inner ℝ (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
        simp only [Finset.sum_insert hp]
        rw [inner_add_left, ih]
  have hMeanLocal (p : Plaq) :
      inner ℝ (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
        (L (1 : C(Cfg, ℝ))) =
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar :=
    p4Q2PZ37AAI_originalLocalPlaquetteHaar_inner_unit_eq_integral H p
  calc
    inner ℝ W U =
        inner ℝ (L (p4Q2JI_actualSpatialWilsonContinuous H))
          (L (1 : C(Cfg, ℝ))) := by
      change inner ℝ (W : Lp ℝ 2 haar) (U : Lp ℝ 2 haar) = _
      rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H,
        p4Q2JU_originalPhysicalUnit_coe_eq_toLp H]
    _ = inner ℝ (∑ p : Plaq,
          L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) := by
      rw [p4Q2PZ37AAI_originalSpatialWilsonHaar_eq_finsetSum H]
    _ = ∑ p : Plaq, inner ℝ
          (L (p4Q2LO_originalLocalPlaquetteContinuous H p))
          (L (1 : C(Cfg, ℝ))) := by
      simpa only using hInnerSum Finset.univ
    _ = ∑ p : Plaq,
          ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hMeanLocal p

/-- The actual original centered Gauss-law PHYSICAL tangent
represented in the original spatial Haar-L² carrier is IDENTICAL
to one half of the AAF centered genuine plaquette synthesis.
The original two interacting Wilson posteriors remain unchanged. -/
theorem p4Q2PZ37AAI_originalCenteredPhysicalFormula_coe_eq_halfHaarSynthesis
    (H : ℕ) :
    (((1 / 2 : ℝ) •
      (p4Q2JU_originalSpatialWilsonPhysicalSource H -
        (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) •
          periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
      Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)) =
    (1 / 2 : ℝ) •
      p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H (fun _ => 1) := by
  classical
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  let haar := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let L : C(Cfg, ℝ) →L[ℝ] Lp ℝ 2 haar :=
    ContinuousMap.toLp 2 haar ℝ
  let Plaq := PeriodicHypercubicEvenSpatialSlicePlaquette H
  let Phys := periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let W : Phys := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let U : Phys := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let w : ℝ := inner ℝ W U
  have hMean : w = ∑ p : Plaq,
      ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar :=
    p4Q2PZ37AAI_originalPhysicalWilsonMean_eq_plaquetteHaarSum H
  have hUncentered :
      (W : Lp ℝ 2 haar) =
        ∑ p : Plaq, L (p4Q2LO_originalLocalPlaquetteContinuous H p) := by
    rw [p4Q2JU_originalSpatialWilsonPhysicalSource_coe_eq_toLp H]
    exact p4Q2PZ37AAI_originalSpatialWilsonHaar_eq_finsetSum H
  have hUnit : (U : Lp ℝ 2 haar) = L (1 : C(Cfg, ℝ)) :=
    p4Q2JU_originalPhysicalUnit_coe_eq_toLp H
  have hCenterSum :
      (∑ p : Plaq, p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p) =
        (∑ p : Plaq, L (p4Q2LO_originalLocalPlaquetteContinuous H p)) -
          (∑ p : Plaq,
            ∫ A, p4Q2LO_originalLocalPlaquetteContinuous H p A ∂haar) •
              L (1 : C(Cfg, ℝ)) := by
    simp only [p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource,
      Finset.sum_sub_distrib, Finset.sum_smul]
    rfl
  unfold p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis
  simp only [one_smul]
  change (((1 / 2 : ℝ) • (W - w • U) : Phys) : Lp ℝ 2 haar) =
    (1 / 2 : ℝ) •
      (∑ p : Plaq, p4Q2PZ37AAI_originalCenteredPlaquetteHaarSource H p)
  rw [Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_smul]
  rw [hCenterSum, ← hMean, ← hUncentered, ← hUnit]

/-- The PHYSICAL Gauss-law normalized centered Wilson tangent,
not a substitute source, has a true Haar-L² squared norm bounded
by 6 times the ACTUAL original spatial plaquette count. -/
theorem p4Q2PZ37AAI_originalCenteredPhysicalFormulaNorm_sq_le_six_plaquetteCount
    (H : ℕ) :
    ‖((1 / 2 : ℝ) •
      (p4Q2JU_originalSpatialWilsonPhysicalSource H -
        (inner ℝ (p4Q2JU_originalSpatialWilsonPhysicalSource H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)) •
          periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) :
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖^2 ≤
      6 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  let W := p4Q2JU_originalSpatialWilsonPhysicalSource H
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let V : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    (1 / 2 : ℝ) • (W - (inner ℝ W U) • U)
  let S := p4Q2PZ37AAI_originalCenteredHaarPlaquetteSynthesis H (fun _ => 1)
  have hEq : ‖V‖ = ‖(1 / 2 : ℝ) • S‖ := by
    change ‖(V : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))‖ =
      ‖(1 / 2 : ℝ) • S‖
    exact congrArg norm
      (p4Q2PZ37AAI_originalCenteredPhysicalFormula_coe_eq_halfHaarSynthesis H)
  have hSq : ‖V‖^2 = (1 / 4 : ℝ) * ‖S‖^2 := by
    rw [hEq, norm_smul, Real.norm_eq_abs]
    norm_num [mul_pow]
  have hBessel :
      ‖S‖^2 ≤ 24 *
        (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) :=
    p4Q2PZ37AAI_originalCenteredHaarPlaquetteUnitSum_sq_le_card H
  dsimp [V] at hSq ⊢
  linarith

/-- The genuine spatial plaquette index is never empty. This is
witnessed by an ORIGINAL coordinate plaquette, not by a proxy count. -/
theorem p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos (H : ℕ) :
    (0 : ℝ) <
      (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  classical
  have hNat : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) :=
    Fintype.card_pos_iff.mpr
      ⟨pz37zaSpatialPlaquetteCoordinateFamily H 0⟩
  exact_mod_cast hNat

/-- The ZW named PHYSICAL Hilbert tangent is definitionally the
original AAG half-centered Wilson source; its Haar-synthesized upper
bound holds in the ORIGINAL Gauss-law physical Hilbert metric. -/
theorem p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount
    (H : ℕ) :
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
      6 * (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
  exact p4Q2PZ37AAI_originalCenteredPhysicalFormulaNorm_sq_le_six_plaquetteCount H

/-- Pure ordered-field step used to distinguish a genuine upper
source norm from an independent lower posterior Gram estimate. -/
private theorem p4Q2PZ37AAI_scaledNorm_le_frameQuarter
    (P m N : ℝ) (hP : 0 < P) (hm : 0 ≤ m)
    (hN : N ≤ 6 * P) :
    (m / (24 * P)) * N ≤ m / 4 := by
  have hCoeff : 0 ≤ m / (24 * P) := div_nonneg hm (by positivity)
  calc
    (m / (24 * P)) * N ≤ (m / (24 * P)) * (6 * P) :=
      mul_le_mul_of_nonneg_left hN hCoeff
    _ = m / 4 := by
      field_simp [ne_of_gt hP]
      <;> ring

/-- A true ORIGINAL interacting-posterior centered two-source Gram
floor m/4 controls the physical source norm at rate m/(24 P_H).
It assumes no positivity of the product-Haar Gram from the posterior. -/
theorem p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 ≤ m)
    (hGram : m / 4 ≤ p4Q2PZ37ZX_originalCenteredGLGramValue H b hb) :
    (m / (24 * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) *
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤
        p4Q2PZ37ZX_originalCenteredGLGramValue H b hb := by
  let P : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)
  have hP : 0 < P := p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos H
  have hNorm :
      ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 ≤ 6 * P :=
    p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount H
  exact (p4Q2PZ37AAI_scaledNorm_le_frameQuarter P m
    ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2
    hP hm hNorm).trans hGram

/-- Concrete full-link true posterior Rayleigh versus actual spatial
plaquette count: this lower bound uses NO Haar replacement. -/
theorem p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
    (H : ℕ) (b : ℝ) (hb : 0 < b)
    (m : ℝ) (hm : 0 ≤ m)
    (hGram : m / 4 ≤ p4Q2PZ37ZX_originalCenteredGLGramValue H b hb) :
    m / (24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) ≤
      p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb := by
  have hNorm :
      0 < ‖p4Q2PZ37ZW_originalCenteredPhysicalDirection H‖^2 :=
    pow_pos (norm_pos_iff.mpr
      (p4Q2PZ37ZW_originalCenteredDirection_ne_zero H)) 2
  unfold p4Q2PZ37AAH_originalExactCenteredRayleighFloor
  rw [p4Q2PZ37ZX_originalCenteredRayleigh_eq_originalGram_div_physicalNorm]
  exact (le_div_iff₀ hNorm).mpr
    (p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
      H b hb m hm hGram)

/-- At every genuine finite H,b>0, ZP supplies its actual original
posterior two-mode frame constant m>0. With the actual Haar source norm
upper bound this yields a positive quantitative Rayleigh floor
m/(24P_H), and AAE constructs a true positive fine interval with
R(F_t)>=m/(48P_H). The constant remains volume dependent. -/
theorem p4Q2PZ37AAI_originalPosterior_exists_plaquetteScaledFineRadius
    (H : ℕ) (b : ℝ) (hb : 0 < b) :
    ∃ m : ℝ, 0 < m ∧
      m / (24 * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) ≤
        p4Q2PZ37AAH_originalExactCenteredRayleighFloor H b hb ∧
      0 < p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b
        (m / (24 * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) ∧
      ∀ t : Set.Ici (0 : ℝ), 0 < (t : ℝ) →
        (t : ℝ) < p4Q2PZ37AAE_originalCertifiedPositiveFineRadius H b
          (m / (24 * (Fintype.card
            (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) →
        (m / (24 * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ))) / 2 ≤
          p4Q2PZ37ZG_originalFullLinkGL_physicalRayleigh H b hb
            (p4Q2PZ37ZE_originalPhysicalCancellation H t) := by
  let p := pz37zaSpatialPlaquetteCoordinateFamily H 0
  let e : PeriodicHypercubicEvenSpatialSliceLink H := (p.1, p.2.1.1)
  let A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 :=
    fun _ => 1
  obtain ⟨m, hm, hGram, _hRayleigh⟩ :=
    p4Q2PZ37ZX_originalCenteredGL_exists_quantitativeRayleighFloor
      H b hb e e A A
  have hP := p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos H
  have hc : 0 < m / (24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) :=
    div_pos hm (by positivity)
  have hSourceGram :=
    p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
      H b hb m hm.le hGram
  have hFine :=
    p4Q2PZ37AAE_originalCertifiedRadius_positiveRayleighFloor
      H b hb
      (m / (24 * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)))
      hc hSourceGram
  refine ⟨m, hm, ?_, hFine.1, ?_⟩
  · exact p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
      H b hb m hm.le hGram
  · intro t ht htρ
    exact (hFine.2 t ht htρ).2

/-- Entirely original *sufficient* all-volume criterion.
An extensive lower bound m_H >= 24*c*P_H for genuine full-link,
two-Wilson-posterior physical coefficient-frames would produce a
common fine-ZERO centered physical Rayleigh floor c>0. Existence
of such m_H is NOT asserted, nor does this provide a common fine
interval: AAB/AAD's global budget obstruction remains untouched. -/
theorem p4Q2PZ37AAI_uniformCenteredFineZeroFloor_of_extensivePosteriorFrame
    (b : ℕ → ℝ) (hb : ∀ H, 0 < b H)
    (m : ℕ → ℝ) (hm : ∀ H, 0 < m H)
    (c : ℝ) (hc : 0 < c)
    (hFrame : ∀ H : ℕ, ∀ a : Fin 2 → ℝ,
      m H * ‖a‖^2 ≤
        p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
          H (b H) (hb H).le
          (p4Q2PZ37ZN_originalStaticPhysicalSource H a)
          (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)))
    (hExtensive : ∀ H : ℕ,
      24 * c * (Fintype.card
        (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) ≤ m H) :
    ∀ H : ℕ, 0 < c ∧
      c ≤ p4Q2PZ37AAH_originalExactCenteredRayleighFloor H (b H) (hb H) := by
  intro H
  have hP : 0 < (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) :=
    p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos H
  have hDen : 0 < 24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by
    positivity
  have hRatio : c ≤ m H / (24 * (Fintype.card
      (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) := by
    apply (le_div_iff₀ hDen).mpr
    calc
      c * (24 * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ)) =
        24 * c * (Fintype.card
          (PeriodicHypercubicEvenSpatialSlicePlaquette H) : ℝ) := by ring
      _ ≤ m H := hExtensive H
  have hGram : m H / 4 ≤
      p4Q2PZ37ZX_originalCenteredGLGramValue H (b H) (hb H) := by
    rw [p4Q2PZ37ZX_originalCenteredGram_eq_originalGLMass]
    exact p4Q2PZ37ZX_originalCenteredGLMass_ge_quarter_floor
      H (b H) (hb H) (m H) (hm H) (hFrame H)
  exact ⟨hc, hRatio.trans
    (p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
      H (b H) (hb H) (m H) (hm H).le hGram)⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalSpatialPlaquetteCount_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalCenteredPhysicalNorm_sq_le_six_plaquetteCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalCenteredGram_ge_plaquetteScaledNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalCenteredRayleigh_ge_frameFloor_div_twentyFourCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_originalPosterior_exists_plaquetteScaledFineRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AAI_uniformCenteredFineZeroFloor_of_extensivePosteriorFrame
