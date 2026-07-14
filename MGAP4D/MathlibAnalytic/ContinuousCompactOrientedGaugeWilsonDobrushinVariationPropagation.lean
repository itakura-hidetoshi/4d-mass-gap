import MGAP4D.MathlibAnalytic.SpecialUnitaryCompactOrientedBoundedTestInfluence
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Exact compact-Haar one-link conditional expectation of a bounded continuous
observable, kept pointwise before passage to the Gibbs `L²` projection. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g : C.base.Gauge,
    O (C.base.replaceLink A target g)
      ∂C.singleLinkConditionalMeasure A target

/-- A bounded continuous observable pulled back to one compact link is
integrable against the exact conditional Haar--Gibbs law. -/
theorem continuous_compact_oriented_singleLinkObservable_integrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Integrable
      (fun g : C.base.Gauge => O (C.base.replaceLink A target g))
      (C.singleLinkConditionalMeasure A target) := by
  letI : IsProbabilityMeasure (C.singleLinkConditionalMeasure A target) :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  exact
    (O.continuous.comp
      (continuous_compact_oriented_replaceLink C A target)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- A proof-relevant physical-link oscillation bound for a real function on the
compact oriented configuration space. -/
structure ContinuousCompactOrientedGaugeWilsonLinkVariationBound
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (F : C.base.Configuration → ℝ) where
  variation : C.base.geometry.Edge → ℝ
  variation_nonneg : ∀ e : C.base.geometry.Edge, 0 ≤ variation e
  variation_bound :
    ∀ (e : C.base.geometry.Edge) (A B : C.base.Configuration),
      C.base.AgreeOffLink A B e → |F A - F B| ≤ variation e

/-- A bounded continuous observable variation profile equipped with a midpoint
center on every one-link fiber. -/
structure ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    extends ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => O A) where
  fiberCenter : C.base.Configuration → C.base.geometry.Edge → ℝ
  fiber_radius_bound :
    ∀ (A : C.base.Configuration) (e : C.base.geometry.Edge) (g : C.base.Gauge),
      |O (C.base.replaceLink A e g) - fiberCenter A e| ≤ variation e / 2

/-- A common target replacement preserves agreement away from a separately
specified physical source link. -/
theorem compact_oriented_replaceLink_agreeOffLink
    (L : CompactOrientedGaugeWilsonSystem)
    (A B : L.Configuration)
    (target source : L.geometry.Edge)
    (g : L.Gauge)
    (hAgree : L.AgreeOffLink A B source) :
    L.AgreeOffLink
      (L.replaceLink A target g)
      (L.replaceLink B target g)
      source := by
  intro e he
  by_cases ht : e = target
  · subst e
    simp
  · simp [CompactOrientedGaugeWilsonSystem.replaceLink, ht, hAgree e he]

/-- Linkwise variation after one exact target-link conditional expectation. -/
noncomputable def continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (target source : C.base.geometry.Edge) : ℝ := by
  classical
  exact if source = target then 0
    else variation source + D.influence target source * variation target

/-- The compact Dobrushin-updated variation profile is nonnegative. -/
theorem continuous_compact_oriented_dobrushinUpdatedVariation_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (target source : C.base.geometry.Edge) :
    0 ≤ continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
      D variation target source := by
  classical
  unfold continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
  by_cases h : source = target
  · simp [h]
  · simp only [h, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

/-- Two configurations agreeing away from the resampled link give the same
pointwise conditional expectation. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectationBCF_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalExpectationBCF O A target =
      C.singleLinkConditionalExpectationBCF O B target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
    C A B target hAgree]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [compact_oriented_replaceLink_eq_of_agreeOffLink
    C.base A B target g hAgree]

/-- Under one fixed probability law, a uniform pointwise difference controls the
corresponding expectation difference. -/
theorem continuous_compact_oriented_conditionalIntegral_direct_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hA hB : C.base.Gauge → ℝ)
    (hhA : Continuous hA)
    (hhB : Continuous hB)
    (sourceBound : ℝ)
    (hSourceBound : ∀ g : C.base.Gauge, |hA g - hB g| ≤ sourceBound) :
    |(∫ g, hA g ∂C.singleLinkConditionalMeasure A target) -
      (∫ g, hB g ∂C.singleLinkConditionalMeasure A target)| ≤ sourceBound := by
  let μ := C.singleLinkConditionalMeasure A target
  letI : IsProbabilityMeasure μ :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  have hAInt : Integrable hA μ :=
    hhA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hBInt : Integrable hB μ :=
    hhB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDiffInt : Integrable (fun g => hA g - hB g) μ := hAInt.sub' hBInt
  have hAbsDiffInt : Integrable (fun g => |hA g - hB g|) μ := by
    simpa [Real.norm_eq_abs] using hDiffInt.norm
  have hConstInt : Integrable (fun _ : C.base.Gauge => sourceBound) μ :=
    integrable_const sourceBound
  change
    |(∫ g, hA g ∂μ) - (∫ g, hB g ∂μ)| ≤ sourceBound
  rw [← integral_sub hAInt hBInt]
  calc
    |∫ g, hA g - hB g ∂μ| ≤ ∫ g, |hA g - hB g| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _g : C.base.Gauge, sourceBound ∂μ := by
      apply integral_mono hAbsDiffInt hConstInt
      intro g
      exact hSourceBound g
    _ = sourceBound := by simp

/-- The bounded-test Dobrushin estimate scales sharply to tests centered in a
fiber interval of radius `radius`. -/
theorem continuous_compact_oriented_dobrushin_centeredTest_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source)
    (h : C.base.Gauge → ℝ)
    (hh : Continuous h)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius : ∀ g : C.base.Gauge, |h g - center| ≤ radius) :
    |(∫ g, h g ∂C.singleLinkConditionalMeasure A target) -
      (∫ g, h g ∂C.singleLinkConditionalMeasure B target)| ≤
        2 * D.influence target source * radius := by
  let μA := C.singleLinkConditionalMeasure A target
  let μB := C.singleLinkConditionalMeasure B target
  letI : IsProbabilityMeasure μA :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C A target
  letI : IsProbabilityMeasure μB :=
    continuous_compact_oriented_singleLinkConditionalMeasure_isProbabilityMeasure
      C B target
  by_cases hRadiusZero : radius = 0
  · have hConst : h = fun _ : C.base.Gauge => center := by
      funext g
      have hle := hRadius g
      rw [hRadiusZero] at hle
      have hz : |h g - center| = 0 := le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    simp [μA, μB, hConst, hRadiusZero]
  · have hRadiusPos : 0 < radius := lt_of_le_of_ne hRadiusNonneg (Ne.symm hRadiusZero)
    let phi : C.base.Gauge → ℝ := fun g => (h g - center) / radius
    have hphiContinuous : Continuous phi := by
      unfold phi
      fun_prop
    have hphiBound : ∀ g : C.base.Gauge, |phi g| ≤ 1 := by
      intro g
      unfold phi
      rw [abs_div, abs_of_pos hRadiusPos]
      apply (div_le_iff₀ hRadiusPos).2
      simpa only [one_mul] using hRadius g
    have hD := D.conditionalIntegral_difference_abs_le
      target source A B hAgree phi hphiContinuous.stronglyMeasurable hphiBound
    have hphiAInt : Integrable phi μA :=
      hphiContinuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hphiBInt : Integrable phi μB :=
      hphiContinuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hAIdentity :
        (∫ g, h g ∂μA) = radius * (∫ g, phi g ∂μA) + center := by
      calc
        (∫ g, h g ∂μA) = ∫ g, radius * phi g + center ∂μA := by
          apply integral_congr_ae
          filter_upwards [] with g
          unfold phi
          field_simp [ne_of_gt hRadiusPos]
          ring
        _ = radius * (∫ g, phi g ∂μA) + center := by
          rw [integral_add (hphiAInt.const_mul radius) (integrable_const center),
            integral_const_mul]
          simp
    have hBIdentity :
        (∫ g, h g ∂μB) = radius * (∫ g, phi g ∂μB) + center := by
      calc
        (∫ g, h g ∂μB) = ∫ g, radius * phi g + center ∂μB := by
          apply integral_congr_ae
          filter_upwards [] with g
          unfold phi
          field_simp [ne_of_gt hRadiusPos]
          ring
        _ = radius * (∫ g, phi g ∂μB) + center := by
          rw [integral_add (hphiBInt.const_mul radius) (integrable_const center),
            integral_const_mul]
          simp
    change
      |(∫ g, h g ∂μA) - (∫ g, h g ∂μB)| ≤
        2 * D.influence target source * radius
    rw [hAIdentity, hBIdentity]
    have hAlgebra :
        radius * (∫ g, phi g ∂μA) + center -
            (radius * (∫ g, phi g ∂μB) + center) =
          radius * ((∫ g, phi g ∂μA) - ∫ g, phi g ∂μB) := by ring
    rw [hAlgebra, abs_mul, abs_of_pos hRadiusPos]
    calc
      radius * |(∫ g, phi g ∂μA) - ∫ g, phi g ∂μB| ≤
          radius * (2 * D.influence target source) :=
        mul_le_mul_of_nonneg_left hD hRadiusPos.le
      _ = 2 * D.influence target source * radius := by ring

/-- A centered compact fiber profile gives the sharp Dobrushin variation update
for one exact conditional expectation. -/
theorem continuous_compact_oriented_dobrushin_centeredVariation_conditionalExpectationBCF_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source) :
    |C.singleLinkConditionalExpectationBCF O A target -
        C.singleLinkConditionalExpectationBCF O B target| ≤
      P.variation source + D.influence target source * P.variation target := by
  let hA : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink A target g)
  let hB : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink B target g)
  have hhA : Continuous hA :=
    O.continuous.comp (continuous_compact_oriented_replaceLink C A target)
  have hhB : Continuous hB :=
    O.continuous.comp (continuous_compact_oriented_replaceLink C B target)
  have hSourceBound : ∀ g : C.base.Gauge,
      |hA g - hB g| ≤ P.variation source := by
    intro g
    exact P.variation_bound source
      (C.base.replaceLink A target g)
      (C.base.replaceLink B target g)
      (compact_oriented_replaceLink_agreeOffLink
        C.base A B target source g hAgree)
  have hDirect :=
    continuous_compact_oriented_conditionalIntegral_direct_difference_abs_le
      C A target hA hB hhA hhB (P.variation source) hSourceBound
  have hLaw :=
    continuous_compact_oriented_dobrushin_centeredTest_difference_abs_le
      C D target source A B hAgree hB hhB
      (P.fiberCenter B target) (P.variation target / 2)
      (div_nonneg (P.variation_nonneg target) (by norm_num))
      (P.fiber_radius_bound B target)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectationBCF
  change
    |(∫ g, hA g ∂C.singleLinkConditionalMeasure A target) -
      (∫ g, hB g ∂C.singleLinkConditionalMeasure B target)| ≤
        P.variation source + D.influence target source * P.variation target
  have hSplit :
      (∫ g, hA g ∂C.singleLinkConditionalMeasure A target) -
          (∫ g, hB g ∂C.singleLinkConditionalMeasure B target) =
        ((∫ g, hA g ∂C.singleLinkConditionalMeasure A target) -
          ∫ g, hB g ∂C.singleLinkConditionalMeasure A target) +
        ((∫ g, hB g ∂C.singleLinkConditionalMeasure A target) -
          ∫ g, hB g ∂C.singleLinkConditionalMeasure B target) := by ring
  rw [hSplit]
  calc
    |((∫ g, hA g ∂C.singleLinkConditionalMeasure A target) -
        ∫ g, hB g ∂C.singleLinkConditionalMeasure A target) +
      ((∫ g, hB g ∂C.singleLinkConditionalMeasure A target) -
        ∫ g, hB g ∂C.singleLinkConditionalMeasure B target)| ≤
      |(∫ g, hA g ∂C.singleLinkConditionalMeasure A target) -
        ∫ g, hB g ∂C.singleLinkConditionalMeasure A target| +
      |(∫ g, hB g ∂C.singleLinkConditionalMeasure A target) -
        ∫ g, hB g ∂C.singleLinkConditionalMeasure B target| := abs_add_le _ _
    _ ≤ P.variation source +
        2 * D.influence target source * (P.variation target / 2) :=
      add_le_add hDirect hLaw
    _ = P.variation source +
        D.influence target source * P.variation target := by ring

/-- Package the exact one-link conditional expectation with its updated
physical-link variation bound. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile.conditionalExpectationVariationBound
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target : C.base.geometry.Edge) :
    ContinuousCompactOrientedGaugeWilsonLinkVariationBound C
      (fun A => C.singleLinkConditionalExpectationBCF O A target) := by
  classical
  refine
    { variation := continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
        D P.variation target
      variation_nonneg :=
        continuous_compact_oriented_dobrushinUpdatedVariation_nonneg
          D P.variation P.variation_nonneg target
      variation_bound := ?_ }
  intro source A B hAgree
  by_cases h : source = target
  · subst source
    have hEq :=
      continuous_compact_oriented_singleLinkConditionalExpectationBCF_eq_of_agreeOffLink
        C O A B target hAgree
    rw [hEq]
    simp [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation]
  · simpa [continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation, h] using
      (continuous_compact_oriented_dobrushin_centeredVariation_conditionalExpectationBCF_difference_abs_le
        C D O P target source A B hAgree)

end

end MathlibAnalytic
end MGAP4D