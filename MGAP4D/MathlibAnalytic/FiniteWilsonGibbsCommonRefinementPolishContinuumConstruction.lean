import MGAP4D.MathlibAnalytic.EuclideanYangMillsPolishProjectiveContinuumConstruction
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

section CommonRefinementPolishContinuum

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsCommonRefinementRealization W)
  [hTop : ∀ x, TopologicalSpace (R.fieldValue x)]
  [hBorel : ∀ x, BorelSpace (R.fieldValue x)]
  [hPolish : ∀ x, PolishSpace (R.fieldValue x)]

local instance commonRefinementProjectedTopologicalSpace
    (x : EuclideanFourSpace) :
    TopologicalSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
  hTop x

local instance commonRefinementProjectedBorelSpace
    (x : EuclideanFourSpace) :
    BorelSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
  hBorel x

local instance commonRefinementProjectedPolishSpace
    (x : EuclideanFourSpace) :
    PolishSpace
      (R.toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
  hPolish x

/-- Remaining analytic data needed after a common-refinement Wilson family has
already supplied the projective finite-dimensional probability laws. -/
abbrev FiniteWilsonGibbsCommonRefinementPolishAnalyticData :=
  EuclideanYangMillsPolishContinuumAnalyticData
    R.toProjectiveRealization.toProjectiveCylinderFamily

/-- The canonical Polish Kolmogorov continuum construction generated from the
common-refinement Wilson marginal family. -/
noncomputable def
    finiteWilsonGibbsCommonRefinementPolishContinuumConstruction
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R) :
    EuclideanYangMillsProjectiveContinuumMeasureConstruction
      R.toProjectiveRealization.toProjectiveCylinderFamily :=
  D.toContinuumConstruction

/-- Full typed certificate joining common finite Wilson refinements to the
canonical Polish Kolmogorov continuum measure. -/
noncomputable def
    finiteWilsonGibbsCommonRefinementPolishContinuumCertificate
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R) :
    FiniteWilsonGibbsCommonRefinementContinuumMeasureCertificate
      R (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D) :=
  finiteWilsonGibbsCommonRefinementContinuumMeasureCertificate
    R (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D)

/-- The canonical continuum measure recovers every common-refinement Wilson
Gibbs pushforward marginal. -/
theorem finite_wilson_common_refinement_polish_recovers_marginal
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R)
    (J : Finset EuclideanFourSpace) :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure.map
        J.restrict =
      (W.system (R.scale J)).gibbsMeasure.map (R.observe J) :=
  finite_wilson_common_refinement_continuum_recovers_marginal
    (finiteWilsonGibbsCommonRefinementPolishContinuumCertificate R D) J

/-- Every measurable continuum cylinder is exactly its selected finite Wilson
Gibbs observation probability. -/
theorem finite_wilson_common_refinement_polish_cylinder
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R)
    (J : Finset EuclideanFourSpace)
    {s : Set (∀ x : J, R.fieldValue x)}
    (hs : MeasurableSet s) :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure
        (cylinder J s) =
      (W.system (R.scale J)).gibbsMeasure ((R.observe J) ⁻¹' s) :=
  (finiteWilsonGibbsCommonRefinementPolishContinuumCertificate R D).continuumCylinderIsWilsonGibbs
    J s hs

/-- The common-refinement Polish continuum measure is a probability measure. -/
theorem finite_wilson_common_refinement_polish_probability
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R) :
    IsProbabilityMeasure
      (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure :=
  finite_wilson_common_refinement_continuum_probability
    (finiteWilsonGibbsCommonRefinementPolishContinuumCertificate R D)

/-- The canonical measure is unique among measures realizing the same Wilson
marginal family. -/
theorem finite_wilson_common_refinement_polish_unique
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R)
    (ν : Measure
      R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration)
    (hν : IsProjectiveLimit ν
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal) :
    ν =
      (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).limit.continuumMeasure :=
  finite_wilson_common_refinement_continuum_unique
    (finiteWilsonGibbsCommonRefinementPolishContinuumCertificate R D) ν hν

/-- Once the remaining analytic OS properties are supplied, the canonical
Wilson--Kolmogorov continuum package is ready for the reconstruction bridge. -/
theorem finite_wilson_common_refinement_polish_measure_package_ready
    (D : FiniteWilsonGibbsCommonRefinementPolishAnalyticData R) :
    (finiteWilsonGibbsCommonRefinementPolishContinuumConstruction R D).toMeasurePackage.ready :=
  finite_wilson_common_refinement_continuum_measure_package_ready
    (finiteWilsonGibbsCommonRefinementPolishContinuumCertificate R D)

end CommonRefinementPolishContinuum

end

end MathlibAnalytic
end MGAP4D
