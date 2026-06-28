import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonSingleLinkConditional

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The compact one-link Boltzmann factor depends only on the off-link fiber. -/
theorem continuous_compact_oriented_singleLinkBoltzmannFactor_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target)
    (g : C.base.Gauge) :
    C.singleLinkBoltzmannFactor A target g =
      C.singleLinkBoltzmannFactor B target g := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  rw [compact_oriented_replaceLink_eq_of_agreeOffLink
    C.base A B target g hAgree]

/-- The compact one-link partition function is constant on each off-link
fiber. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkPartitionFunction A target =
      C.singleLinkPartitionFunction B target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  apply integral_congr_ae
  filter_upwards [] with g
  exact
    continuous_compact_oriented_singleLinkBoltzmannFactor_eq_of_agreeOffLink
      C A B target hAgree g

/-- The exact compact one-link conditional measure depends only on the
configuration away from the resampled physical link. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalMeasure A target =
      C.singleLinkConditionalMeasure B target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  apply congrArg
    (fun exponent : C.base.Gauge → ℝ =>
      (normalizedCompactHaar C.base.Gauge).tilted exponent)
  funext g
  rw [compact_oriented_replaceLink_eq_of_agreeOffLink
    C.base A B target g hAgree]

/-- Pre-updating the physical link being resampled does not alter its exact
Haar conditional law. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (h : C.base.Gauge) :
    C.singleLinkConditionalMeasure
        (C.base.replaceLink A target h) target =
      C.singleLinkConditionalMeasure A target := by
  apply
    continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
  intro e he
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, he]

/-- Exact Haar conditional expectation of a real observable after resampling
one physical link. -/
def ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) : ℝ :=
  ∫ g, f (C.base.replaceLink A target g)
    ∂C.singleLinkConditionalMeasure A target

/-- Native compact conditional expectation is constant on off-link fibers. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ)
    (A B : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (hAgree : C.base.AgreeOffLink A B target) :
    C.singleLinkConditionalExpectation f A target =
      C.singleLinkConditionalExpectation f B target := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalExpectation
  rw [continuous_compact_oriented_singleLinkConditionalMeasure_eq_of_agreeOffLink
    C A B target hAgree]
  apply integral_congr_ae
  filter_upwards [] with g
  rw [compact_oriented_replaceLink_eq_of_agreeOffLink
    C.base A B target g hAgree]

/-- Pre-updating the resampled link does not change compact conditional
expectation. -/
theorem continuous_compact_oriented_singleLinkConditionalExpectation_replaceLink
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : C.base.Configuration → ℝ)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (h : C.base.Gauge) :
    C.singleLinkConditionalExpectation f
        (C.base.replaceLink A target h) target =
      C.singleLinkConditionalExpectation f A target := by
  apply
    continuous_compact_oriented_singleLinkConditionalExpectation_eq_of_agreeOffLink
  intro e he
  simp [CompactOrientedGaugeWilsonSystem.replaceLink, he]

end

end MathlibAnalytic
end MGAP4D
