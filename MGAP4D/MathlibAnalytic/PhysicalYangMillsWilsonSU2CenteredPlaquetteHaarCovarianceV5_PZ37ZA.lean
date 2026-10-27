import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoContextGIHaarBesselV5_PZ37ZA
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialPlaquetteOverlapBound
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# PZ37ZA — actual centered Wilson plaquette product-Haar covariance

The measure below is exactly the original spatial Haar L2 reference on
which the already constructed GI continuous linear maps act. It is NOT a
replacement of either interacting posterior. Disjoint actual link supports
are independent under this original reference, hence centered sources are
orthogonal. Each original Wilson energy lies in [0,2], so its centered L2
norm is at most 1. The existing genuine incidence bound then gives 24.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Matrix ProbabilityTheory
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance pz37zaCov_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance pz37zaCov_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance pz37zaCov_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance pz37zaCov_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance pz37zaCov_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance pz37zaCov_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
private noncomputable instance pz37zaCov_plaqFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSlicePlaquette H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint
section Spatial
variable (H : ℕ)
local notation "Gauge" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "μ" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "L" => ContinuousMap.toLp 2 μ ℝ
local notation "W" => p4Q2LO_originalLocalPlaquetteContinuous H
local notation "V" => p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource H

noncomputable def p4Q2PZ37ZA_centeredPlaquetteContinuous (p : Plaq) : C(Cfg, ℝ) :=
  W p - (∫ A, W p A ∂μ) • (1 : C(Cfg, ℝ))

local notation "VC" => p4Q2PZ37ZA_centeredPlaquetteContinuous H

theorem p4Q2PZ37ZA_centeredPlaquette_toLp (p : Plaq) : L (VC p) = V p := by
  simp only [p4Q2PZ37ZA_centeredPlaquetteContinuous,
    p4Q2PZ37ZA_originalCenteredPlaquetteHaarSource, map_sub, map_smul]

private theorem pz37za_toLp_inner (f g : C(Cfg, ℝ)) :
    ⟪L f, L g⟫_ℝ = ∫ A, f A * g A ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ f,
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) μ g] with A hf hg
  rw [hf, hg]
  simp only [RCLike.inner_apply, star_trivial]
  ring

private theorem pz37za_centered_integrable (p : Plaq) : Integrable (VC p) μ :=
  memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := 1) μ ℝ (VC p))

private theorem pz37za_centered_integral_zero (p : Plaq) :
    (∫ A, VC p A ∂μ) = 0 := by
  have hW : Integrable (W p) μ :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (p := 1) μ ℝ (W p))
  change (∫ A, W p A - (∫ B, W p B ∂μ) * 1 ∂μ) = 0
  simp only [mul_one]
  rw [integral_sub hW (integrable_const _)]
  simp

/-- True centered Wilson source has variance at most one on original Haar. -/
theorem p4Q2PZ37ZA_centeredPlaquette_norm_le_one (p : Plaq) : ‖V p‖ ≤ 1 := by
  let m : ℝ := ∫ A, W p A ∂μ
  let u := L (1 : C(Cfg, ℝ))
  let x := L (W p)
  have hu : ‖u‖ = 1 := p4Q2LR_originalHaarUnit_norm H
  have hinner : ⟪x, u⟫_ℝ = m := by
    simpa only [x, u, ContinuousMap.one_apply, mul_one, m] using
      pz37za_toLp_inner H (W p) (1 : C(Cfg, ℝ))
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
private noncomputable def pz37za_supportExtend (p : Plaq)
    (a : pz37zaSpatialPlaquetteSupport H p → Gauge) : Cfg := by
  classical
  exact fun e => if h : e ∈ pz37zaSpatialPlaquetteSupport H p then a ⟨e, h⟩ else 1

private theorem pz37za_supportExtend_continuous (p : Plaq) :
    Continuous (pz37za_supportExtend H p) := by
  classical
  apply continuous_pi
  intro e
  by_cases he : e ∈ pz37zaSpatialPlaquetteSupport H p
  · simpa [pz37za_supportExtend, he] using
      (continuous_apply (⟨e, he⟩ : pz37zaSpatialPlaquetteSupport H p))
  · simp only [pz37za_supportExtend, he, dite_false]
    exact continuous_const

private theorem pz37za_centered_support_restrict (p : Plaq) (A : Cfg) :
    VC p (pz37za_supportExtend H p (fun e => A e)) = VC p A := by
  classical
  have he (k : Fin 4) :
      pz37zaSpatialPlaquetteBoundary H p k ∈ pz37zaSpatialPlaquetteSupport H p :=
    Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  simp only [pz37zaSpatialPlaquetteBoundary, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three] at h0 h1 h2 h3
  simp [p4Q2PZ37ZA_centeredPlaquetteContinuous,
    p4Q2LO_originalLocalPlaquetteContinuous_apply,
    periodicHypercubicEvenSpatialSlicePlaquetteHolonomy,
    pz37za_supportExtend, h0, h1, h2, h3]

/-- Disjoint true link supports imply orthogonality on the ACTUAL reference Haar
L2 carrier. No assertion of independence under either Wilson posterior. -/
theorem p4Q2PZ37ZA_centeredPlaquette_inner_zero_of_disjoint
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
  have hpmeas : Measurable (fun a => VC p (pz37za_supportExtend H p a)) :=
    ((VC p).continuous.comp (pz37za_supportExtend_continuous H p)).measurable
  have hqmeas : Measurable (fun a => VC q (pz37za_supportExtend H q a)) :=
    ((VC q).continuous.comp (pz37za_supportExtend_continuous H q)).measurable
  have hind : IndepFun (VC p) (VC q) μ := by
    have h := hrestrict.comp hpmeas hqmeas
    apply h.congr
    · filter_upwards with A
      exact pz37za_centered_support_restrict H p A
    · filter_upwards with A
      exact pz37za_centered_support_restrict H q A
  rw [← p4Q2PZ37ZA_centeredPlaquette_toLp H p,
    ← p4Q2PZ37ZA_centeredPlaquette_toLp H q, pz37za_toLp_inner]
  rw [hind.integral_fun_mul_eq_mul_integral
    (pz37za_centered_integrable H p).aestronglyMeasurable
    (pz37za_centered_integrable H q).aestronglyMeasurable,
    pz37za_centered_integral_zero H p, zero_mul]

/-- All absolute Gram row sums of the actual centered plaquette family are
bounded by 24, uniformly in H. Both finite incidence and Haar covariance
premises are discharged above, not assumed. -/
theorem p4Q2PZ37ZA_centeredPlaquette_gram_row_le_twentyFour (p : Plaq) :
    (∑ q : Plaq, |⟪V p, V q⟫_ℝ|) ≤ 24 := by
  classical
  have hentry (q : Plaq) : |⟪V p, V q⟫_ℝ| ≤ 1 := by
    calc
      |⟪V p, V q⟫_ℝ| ≤ ‖V p‖ * ‖V q‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * 1 := mul_le_mul
        (p4Q2PZ37ZA_centeredPlaquette_norm_le_one H p)
        (p4Q2PZ37ZA_centeredPlaquette_norm_le_one H q) (norm_nonneg _) (by norm_num)
      _ = 1 := one_mul _
  have hsum : (∑ q : Plaq, |⟪V p, V q⟫_ℝ|) =
      ∑ q ∈ pz37zaSpatialPlaquetteOverlap H p, |⟪V p, V q⟫_ℝ| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro q _hq hnot
    rw [p4Q2PZ37ZA_centeredPlaquette_inner_zero_of_disjoint H p q
      (pz37zaSpatialPlaquetteSupport_disjoint_of_not_overlap H p q hnot), abs_zero]
  rw [hsum]
  calc
    _ ≤ ∑ _q ∈ pz37zaSpatialPlaquetteOverlap H p, (1 : ℝ) :=
      Finset.sum_le_sum (fun q _ => hentry q)
    _ = ((pz37zaSpatialPlaquetteOverlap H p).card : ℝ) := by simp
    _ ≤ 24 := by exact_mod_cast pz37zaSpatialPlaquetteOverlap_card_le_twentyFour H p

end Spatial
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_centeredPlaquette_norm_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_centeredPlaquette_inner_zero_of_disjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZA_centeredPlaquette_gram_row_le_twentyFour
