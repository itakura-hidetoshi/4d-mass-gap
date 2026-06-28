import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkExpectation
import Mathlib.MeasureTheory.Measure.Tilted

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  Real.exp (C.singleLinkGibbsExponent A target g) /
    C.singleLinkPartitionFunction A target

theorem continuous_compact_oriented_singleLinkConditionalDensity_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    0 < C.singleLinkConditionalDensity A target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  exact div_pos (Real.exp_pos _)
    (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)

theorem continuous_compact_oriented_singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkConditionalDensity A target) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  exact
    (Real.continuous_exp.comp
      (continuous_compact_oriented_singleLinkGibbsExponent C A target)).div_const _

theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target =
      (normalizedCompactHaar C.base.Gauge).withDensity
        (fun g => ENNReal.ofReal
          (C.singleLinkConditionalDensity A target g)) := by
  rfl

theorem continuous_compact_oriented_integral_singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    ∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g
        ∂normalizedCompactHaar C.base.Gauge = 1 := by
  have hZ : C.singleLinkPartitionFunction A target ≠ 0 :=
    ne_of_gt
      (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  change C.singleLinkPartitionFunction A target *
      (C.singleLinkPartitionFunction A target)⁻¹ = 1
  exact mul_inv_cancel₀ hZ

theorem continuous_compact_oriented_singleLinkConditionalExpectation_eq_integral_density
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalExpectation O A target =
      ∫ g : C.base.Gauge,
        C.singleLinkConditionalDensity A target g *
          O (C.base.replaceLink A target g)
        ∂normalizedCompactHaar C.base.Gauge := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  rw [MeasureTheory.integral_tilted]
  simp only [smul_eq_mul]
  rfl

theorem continuous_compact_oriented_singleLinkConditionalDensity_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalDensity A target =
      C.singleLinkConditionalDensity B target := by
  have hExponent :=
    continuous_compact_oriented_singleLinkGibbsExponent_eq_of_agreeOffLink
      C A B target hAgree
  have hPartition :
      C.singleLinkPartitionFunction A target =
        C.singleLinkPartitionFunction B target := by
    unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
    rw [hExponent]
  funext g
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  rw [hExponent, hPartition]

end
end MathlibAnalytic
end MGAP4D
