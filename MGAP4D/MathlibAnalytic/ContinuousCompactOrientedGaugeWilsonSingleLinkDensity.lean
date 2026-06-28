import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkExpectation
import Mathlib.MeasureTheory.Measure.Tilted

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Real Radon--Nikodym density of the exact one-link conditional Gibbs law
with respect to normalized compact Haar measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) : ℝ :=
  Real.exp (C.singleLinkGibbsExponent A target g) /
    C.singleLinkPartitionFunction A target

/-- The exact compact one-link conditional density is strictly positive. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    0 < C.singleLinkConditionalDensity A target g := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  exact div_pos (Real.exp_pos _)
    (continuous_compact_oriented_singleLinkPartitionFunction_pos C A target)

/-- The exact compact one-link conditional density is continuous in the
inserted gauge value. -/
theorem continuous_compact_oriented_singleLinkConditionalDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    Continuous (C.singleLinkConditionalDensity A target) := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalDensity
  exact
    (Real.continuous_exp.comp
      (continuous_compact_oriented_singleLinkGibbsExponent C A target)).div_const _

/-- The exact one-link conditional measure is normalized Haar measure weighted
by the explicit positive density. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_withDensity
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target =
      (normalizedCompactHaar C.base.Gauge).withDensity
        (fun g => ENNReal.ofReal
          (C.singleLinkConditionalDensity A target g)) := by
  rfl

/-- The explicit compact one-link conditional density integrates to one. -/
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
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  field_simp [hZ]

/-- Conditional expectation is the normalized Haar integral against the
explicit one-link density. -/
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

/-- The explicit compact one-link conditional density depends only on the
off-target configuration. -/
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
