import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourcePolishContinuumTheorems
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceProjectiveLimitExistence

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

section SingleSourcePolishIdentification

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
  (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
  [∀ x, TopologicalSpace (R.fieldValue x)]
  [∀ x, BorelSpace (R.fieldValue x)]
  [∀ x, PolishSpace (R.fieldValue x)]
  (D : FiniteWilsonGibbsSingleSourcePolishAnalyticData R)

/-- The Polish Kolmogorov measure and the direct global-observation pushforward
are the same projective-limit measure. -/
theorem finite_wilson_single_source_polish_measure_eq_explicit :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure =
      R.continuumMeasure :=
  finite_wilson_gibbs_single_source_constructed_unique R
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.projectiveLimit

/-- Consequently the canonical Polish continuum law is literally the
pushforward of the fixed finite Wilson Gibbs measure through the global field
observation map. -/
theorem finite_wilson_single_source_polish_measure_eq_globalObserve_map :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure =
      (W.system R.sourceScale).gibbsMeasure.map R.globalObserve := by
  calc
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure =
        R.continuumMeasure :=
      finite_wilson_single_source_polish_measure_eq_explicit R D
    _ = (W.system R.sourceScale).gibbsMeasure.map R.globalObserve := by
      rfl

/-- Audit packet identifying the abstract Kolmogorov construction with the
explicit common-source realization. -/
structure FiniteWilsonGibbsSingleSourcePolishIdentificationCertificate where
  measureEqExplicit :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure =
      R.continuumMeasure
  measureEqGlobalObserveMap :
    (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure =
      (W.system R.sourceScale).gibbsMeasure.map R.globalObserve
  probability :
    IsProbabilityMeasure
      (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure
  projectiveLimit :
    IsProjectiveLimit
      (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.continuumMeasure
      R.toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal

/-- Build the identification certificate from projective-limit uniqueness. -/
noncomputable def finiteWilsonGibbsSingleSourcePolishIdentificationCertificate :
    FiniteWilsonGibbsSingleSourcePolishIdentificationCertificate R D :=
  { measureEqExplicit :=
      finite_wilson_single_source_polish_measure_eq_explicit R D
    measureEqGlobalObserveMap :=
      finite_wilson_single_source_polish_measure_eq_globalObserve_map R D
    probability :=
      finite_wilson_single_source_polish_probability R D
    projectiveLimit :=
      (finiteWilsonGibbsSingleSourcePolishContinuumConstruction R D).limit.projectiveLimit }

end SingleSourcePolishIdentification

end

end MathlibAnalytic
end MGAP4D
