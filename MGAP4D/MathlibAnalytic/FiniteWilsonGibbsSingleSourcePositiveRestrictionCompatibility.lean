import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceBoundedContinuousCylinder

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Compatibility between the finite-coordinate observation of a single-source
projective realization and a distinguished positive-half restriction on the
*same* finite Wilson source.

This structure does not assert any continuum extension, surjectivity, density,
or OS positivity.  Its only content is the concrete same-root identification
that a model-specific periodic Wilson realization must prove. -/
structure FiniteWilsonGibbsSingleSourcePositiveRestrictionCompatibility
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace) where
  positiveRestriction :
    (W.system R.sourceScale).Configuration → (∀ x : J, R.fieldValue x)
  observe_eq : R.observe J = positiveRestriction

namespace FiniteWilsonGibbsSingleSourcePositiveRestrictionCompatibility

variable
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    {J : Finset EuclideanFourSpace}

/-- Pointwise form of the concrete same-root observation identity. -/
theorem observe_apply
    (C : FiniteWilsonGibbsSingleSourcePositiveRestrictionCompatibility R J)
    (A : (W.system R.sourceScale).Configuration) :
    R.observe J A = C.positiveRestriction A := by
  exact congrFun C.observe_eq A

/-- Once the finite observation is identified with the desired positive-half
restriction on the same Wilson source, the existing projective cylinder lift
reads exactly that positive-half restriction.

The proof is only a rewrite of the already-established single-source cylinder
identity; in particular no new approximation or extension hypothesis appears. -/
theorem boundedContinuousCylinderLift_globalObserve
    (C : FiniteWilsonGibbsSingleSourcePositiveRestrictionCompatibility R J)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    (f : BoundedContinuousFunction (∀ x : J, R.fieldValue x) ℝ)
    (A : (W.system R.sourceScale).Configuration) :
    R.toProjectiveRealization.toProjectiveCylinderFamily.boundedContinuousCylinderLift
        J f (R.globalObserve A) =
      f (C.positiveRestriction A) := by
  calc
    R.toProjectiveRealization.toProjectiveCylinderFamily.boundedContinuousCylinderLift
        J f (R.globalObserve A) =
        f (R.observe J A) :=
      finite_wilson_gibbs_single_source_boundedContinuousCylinderLift_globalObserve
        R J f A
    _ = f (C.positiveRestriction A) := congrArg f (C.observe_apply A)

/-- Function-level same-root positive-restriction identity.  This is the form
used when a physical interpolation is later compared with an entire finite
Wilson pullback rather than at a single configuration. -/
theorem boundedContinuousCylinderLift_comp_globalObserve
    (C : FiniteWilsonGibbsSingleSourcePositiveRestrictionCompatibility R J)
    [∀ x, TopologicalSpace (R.fieldValue x)]
    (f : BoundedContinuousFunction (∀ x : J, R.fieldValue x) ℝ) :
    (fun A : (W.system R.sourceScale).Configuration =>
      R.toProjectiveRealization.toProjectiveCylinderFamily.boundedContinuousCylinderLift
        J f (R.globalObserve A)) =
      fun A => f (C.positiveRestriction A) := by
  funext A
  exact C.boundedContinuousCylinderLift_globalObserve f A

end FiniteWilsonGibbsSingleSourcePositiveRestrictionCompatibility

end

end MathlibAnalytic
end MGAP4D
