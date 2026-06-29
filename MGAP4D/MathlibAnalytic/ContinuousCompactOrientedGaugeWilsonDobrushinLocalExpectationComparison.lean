import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonVariationProfile
import MGAP4D.MathlibAnalytic.ContinuousProbabilityDensityTotalVariationDual

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- One compact conditional density controls the expectation difference of two
continuous tests by their uniform pointwise difference. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_direct_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hA hB : C.base.Gauge → ℝ)
    (hhA : Continuous hA)
    (hhB : Continuous hB)
    (sourceBound : ℝ)
    (hSourceNonneg : 0 ≤ sourceBound)
    (hSourceBound : ∀ g : C.base.Gauge, |hA g - hB g| ≤ sourceBound) :
    |(∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g * hA g
        ∂normalizedCompactHaar C.base.Gauge) -
      ∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g * hB g
        ∂normalizedCompactHaar C.base.Gauge| ≤ sourceBound := by
  let p : C.base.Gauge → ℝ := C.singleLinkConditionalDensity A target
  have hp : Continuous p :=
    continuous_compact_oriented_singleLinkConditionalDensity C A target
  have hpInt : Integrable p (normalizedCompactHaar C.base.Gauge) :=
    hp.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace p)
  have hpHAInt : Integrable (fun g : C.base.Gauge => p g * hA g)
      (normalizedCompactHaar C.base.Gauge) :=
    (hp.mul hhA).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpHBInt : Integrable (fun g : C.base.Gauge => p g * hB g)
      (normalizedCompactHaar C.base.Gauge) :=
    (hp.mul hhB).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hProductInt : Integrable
      (fun g : C.base.Gauge => p g * (hA g - hB g))
      (normalizedCompactHaar C.base.Gauge) :=
    (hp.mul (hhA.sub hhB)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hAbsProductInt : Integrable
      (fun g : C.base.Gauge => |p g * (hA g - hB g)|)
      (normalizedCompactHaar C.base.Gauge) := by
    simpa [Real.norm_eq_abs] using hProductInt.norm
  have hUpperInt : Integrable
      (fun g : C.base.Gauge => p g * sourceBound)
      (normalizedCompactHaar C.base.Gauge) :=
    hpInt.mul_const sourceBound
  change
    |(∫ g : C.base.Gauge, p g * hA g
        ∂normalizedCompactHaar C.base.Gauge) -
      ∫ g : C.base.Gauge, p g * hB g
        ∂normalizedCompactHaar C.base.Gauge| ≤ sourceBound
  rw [← integral_sub hpHAInt hpHBInt]
  have hIntegrand :
      (fun g : C.base.Gauge => p g * hA g - p g * hB g) =
        fun g => p g * (hA g - hB g) := by
    funext g
    ring
  rw [hIntegrand]
  calc
    |∫ g : C.base.Gauge, p g * (hA g - hB g)
        ∂normalizedCompactHaar C.base.Gauge| ≤
      ∫ g : C.base.Gauge, |p g * (hA g - hB g)|
        ∂normalizedCompactHaar C.base.Gauge :=
      abs_integral_le_integral_abs
    _ ≤ ∫ g : C.base.Gauge, p g * sourceBound
        ∂normalizedCompactHaar C.base.Gauge := by
      apply integral_mono hAbsProductInt hUpperInt
      intro g
      change |p g * (hA g - hB g)| ≤ p g * sourceBound
      rw [abs_mul, abs_of_nonneg (le_of_lt
        (continuous_compact_oriented_singleLinkConditionalDensity_pos
          C A target g))]
      exact mul_le_mul_of_nonneg_left (hSourceBound g)
        (le_of_lt
          (continuous_compact_oriented_singleLinkConditionalDensity_pos
            C A target g))
    _ = sourceBound := by
      rw [integral_mul_const,
        continuous_compact_oriented_integral_singleLinkConditionalDensity]
      simp

/-- A compact Dobrushin matrix entry controls every centered common-test
conditional expectation difference. -/
theorem continuous_compact_oriented_dobrushin_conditionalDensity_test_difference_abs_le
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
    |(∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g * h g
        ∂normalizedCompactHaar C.base.Gauge) -
      ∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity B target g * h g
        ∂normalizedCompactHaar C.base.Gauge| ≤
      2 * D.influence target source * radius := by
  have hBase :=
    continuous_probabilityDensity_test_difference_abs_le_two_mul_tv_mul_radius
      (normalizedCompactHaar C.base.Gauge)
      (C.singleLinkConditionalDensity A target)
      (C.singleLinkConditionalDensity B target)
      h
      (continuous_compact_oriented_singleLinkConditionalDensity C A target)
      (continuous_compact_oriented_singleLinkConditionalDensity C B target)
      hh
      (continuous_compact_oriented_integral_singleLinkConditionalDensity
        C A target)
      (continuous_compact_oriented_integral_singleLinkConditionalDensity
        C B target)
      center radius hRadiusNonneg hRadius
  have hTV := D.conditionalTotalVariation_le target source A B hAgree
  calc
    |(∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g * h g
        ∂normalizedCompactHaar C.base.Gauge) -
      ∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity B target g * h g
        ∂normalizedCompactHaar C.base.Gauge| ≤
      2 * C.singleLinkConditionalTotalVariation A B target * radius := by
        simpa [ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalTotalVariation]
          using hBase
    _ ≤ 2 * D.influence target source * radius := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hTV (by norm_num)) hRadiusNonneg

/-- Local compact Dobrushin propagation for exact one-link conditional
expectations. -/
theorem continuous_compact_oriented_dobrushin_singleLinkConditionalExpectation_difference_abs_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (target source : C.base.geometry.Edge)
    (A B : C.base.Configuration)
    (hAgree : C.base.AgreeOffLink A B source)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (sourceBound targetRadius center : ℝ)
    (hSourceNonneg : 0 ≤ sourceBound)
    (hSourceBound : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink A target g) -
        O (C.base.replaceLink B target g)| ≤ sourceBound)
    (hTargetRadiusNonneg : 0 ≤ targetRadius)
    (hTargetRadius : ∀ g : C.base.Gauge,
      |O (C.base.replaceLink B target g) - center| ≤ targetRadius) :
    |C.singleLinkConditionalExpectation O A target -
        C.singleLinkConditionalExpectation O B target| ≤
      sourceBound + 2 * D.influence target source * targetRadius := by
  let hA : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink A target g)
  let hB : C.base.Gauge → ℝ :=
    fun g => O (C.base.replaceLink B target g)
  have hhA : Continuous hA :=
    O.continuous.comp (continuous_compact_oriented_replaceLink C A target)
  have hhB : Continuous hB :=
    O.continuous.comp (continuous_compact_oriented_replaceLink C B target)
  have hDirect :=
    continuous_compact_oriented_singleLinkConditionalDensity_direct_difference_abs_le
      C A target hA hB hhA hhB sourceBound hSourceNonneg
      (by intro g; simpa [hA, hB] using hSourceBound g)
  have hLaw :=
    continuous_compact_oriented_dobrushin_conditionalDensity_test_difference_abs_le
      C D target source A B hAgree hB hhB center targetRadius
      hTargetRadiusNonneg
      (by intro g; simpa [hB] using hTargetRadius g)
  rw [continuous_compact_oriented_singleLinkConditionalExpectation_eq_integral_density,
    continuous_compact_oriented_singleLinkConditionalExpectation_eq_integral_density]
  change
    |(∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g * hA g
        ∂normalizedCompactHaar C.base.Gauge) -
      ∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity B target g * hB g
        ∂normalizedCompactHaar C.base.Gauge| ≤
      sourceBound + 2 * D.influence target source * targetRadius
  have hSplit :
      (∫ g : C.base.Gauge,
          C.singleLinkConditionalDensity A target g * hA g
          ∂normalizedCompactHaar C.base.Gauge) -
        ∫ g : C.base.Gauge,
          C.singleLinkConditionalDensity B target g * hB g
          ∂normalizedCompactHaar C.base.Gauge =
      ((∫ g : C.base.Gauge,
          C.singleLinkConditionalDensity A target g * hA g
          ∂normalizedCompactHaar C.base.Gauge) -
        ∫ g : C.base.Gauge,
          C.singleLinkConditionalDensity A target g * hB g
          ∂normalizedCompactHaar C.base.Gauge) +
      ((∫ g : C.base.Gauge,
          C.singleLinkConditionalDensity A target g * hB g
          ∂normalizedCompactHaar C.base.Gauge) -
        ∫ g : C.base.Gauge,
          C.singleLinkConditionalDensity B target g * hB g
          ∂normalizedCompactHaar C.base.Gauge) := by
    ring
  rw [hSplit]
  exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

end
end MathlibAnalytic
end MGAP4D
