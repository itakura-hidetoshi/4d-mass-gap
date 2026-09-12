import MGAP4D.MathlibAnalytic.EuclideanYangMillsMeasureConstructionSpine
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Complete Euclidean Yang--Mills construction certificate extracted from the
continuum measure construction spine.

This layer records only construction-side outputs: finite-volume readiness,
projective and weak-limit readiness, continuum measure construction, gauge-group
construction, interacting continuum limit, gauge-invariant Schwinger functions,
and the measure-side structural theorems.  It does not package a mass-gap theorem
or any publication/export surface. -/
structure EuclideanYangMillsCompleteConstructionCertificate
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  limitReady : S.limitReady
  targetReady : S.toUnconditionalTarget.ready
  measureReady : S.measurePackage.ready
  bridgeMeasureReady : S.bridge.measure.ready
  continuumMeasureConstructed :
    S.continuumFourDimensionalYangMillsMeasureConstructed
  nontrivialCompactGaugeGroupConstructed :
    S.nontrivialCompactGaugeGroupConstructed
  interactingContinuumLimitConstructed :
    S.interactingContinuumLimitConstructed
  gaugeInvariantSchwingerFunctionsConstructed :
    S.gaugeInvariantSchwingerFunctionsConstructed
  reflectionPositivity : S.measurePackage.reflectionPositive
  euclideanInvariance : S.measurePackage.euclideanInvariant
  symmetry : S.measurePackage.symmetric
  clusterProperty : S.measurePackage.clusterProperty
  regularity : S.measurePackage.regularity
  gaugeGroupCompact : S.measurePackage.gaugeGroupCompact
  gaugeGroupNontrivial : S.measurePackage.gaugeGroupNontrivial

namespace EuclideanYangMillsCompleteConstructionCertificate

/-- Build the complete construction certificate from the construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionCertificate S :=
  { limitReady := euclidean_yang_mills_continuum_spine_limit_ready S
    targetReady := euclidean_yang_mills_continuum_spine_unconditional_target_ready S
    measureReady := euclidean_yang_mills_continuum_spine_measure_ready S
    bridgeMeasureReady := euclidean_yang_mills_continuum_spine_bridge_measure_ready S
    continuumMeasureConstructed :=
      S.continuumFourDimensionalYangMillsMeasureConstructed_proof
    nontrivialCompactGaugeGroupConstructed :=
      S.nontrivialCompactGaugeGroupConstructed_proof
    interactingContinuumLimitConstructed :=
      S.interactingContinuumLimitConstructed_proof
    gaugeInvariantSchwingerFunctionsConstructed :=
      S.gaugeInvariantSchwingerFunctionsConstructed_proof
    reflectionPositivity := S.reflectionPositivityPassesToLimit
    euclideanInvariance := S.euclideanInvariancePassesToLimit
    symmetry := S.symmetryPassesToLimit
    clusterProperty := S.clusterPropertyPassesToLimit
    regularity := S.regularityPassesToLimit
    gaugeGroupCompact := S.gaugeGroupCompactTheorem
    gaugeGroupNontrivial := S.gaugeGroupNontrivialTheorem }

/-- Extract continuum measure construction. -/
theorem continuumMeasure
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.continuumFourDimensionalYangMillsMeasureConstructed :=
  C.continuumMeasureConstructed

/-- Extract nontrivial compact gauge-group construction. -/
theorem nontrivialCompactGaugeGroup
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.nontrivialCompactGaugeGroupConstructed :=
  C.nontrivialCompactGaugeGroupConstructed

/-- Extract interacting continuum-limit construction. -/
theorem interactingContinuumLimit
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.interactingContinuumLimitConstructed :=
  C.interactingContinuumLimitConstructed

/-- Extract gauge-invariant Schwinger-function construction. -/
theorem gaugeInvariantSchwingerFunctions
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.gaugeInvariantSchwingerFunctionsConstructed :=
  C.gaugeInvariantSchwingerFunctionsConstructed

/-- Extract measure-package readiness. -/
theorem measurePackageReady
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.measurePackage.ready :=
  C.measureReady

end EuclideanYangMillsCompleteConstructionCertificate

end

end MathlibAnalytic
end MGAP4D
