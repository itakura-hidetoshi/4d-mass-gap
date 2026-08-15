import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence
import MGAP4D.MathlibAnalytic.EuclideanYangMillsProjectiveBoundedContinuousCylinder

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A bounded-continuous projective cylinder observable, evaluated on the
single-source Wilson `globalObserve`, is exactly the original finite-coordinate
observable evaluated on the corresponding finite Wilson observation.

This is the pointwise same-root identity for the projective cylinder layer.  It
uses the already-proved equality
`J.restrict (R.globalObserve A) = R.observe J A`; no extension theorem,
surjectivity, density, OS hypothesis, or continuum identification is inserted. -/
theorem finite_wilson_gibbs_single_source_boundedContinuousCylinderLift_globalObserve
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, R.fieldValue x) ℝ)
    (A : (W.system R.sourceScale).Configuration) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.boundedContinuousCylinderLift
        J f (R.globalObserve A) =
      f (R.observe J A) := by
  rw [EuclideanYangMillsProjectiveCylinderFamily.boundedContinuousCylinderLift_apply]
  rw [finite_wilson_gibbs_single_source_globalObserve_restrict]

/-- Function-level form of the same-root cylinder identity.  Thus precomposing
any lifted continuum cylinder observable with the actual common Wilson source
recovers exactly its finite-coordinate readout. -/
theorem finite_wilson_gibbs_single_source_boundedContinuousCylinderLift_comp_globalObserve
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    (J : Finset EuclideanFourSpace)
    (f : BoundedContinuousFunction (∀ x : J, R.fieldValue x) ℝ) :
    (fun A : (W.system R.sourceScale).Configuration =>
      R.toProjectiveRealization.toProjectiveCylinderFamily.boundedContinuousCylinderLift
        J f (R.globalObserve A)) =
      fun A => f (R.observe J A) := by
  funext A
  exact
    finite_wilson_gibbs_single_source_boundedContinuousCylinderLift_globalObserve
      R J f A

end

end MathlibAnalytic
end MGAP4D
