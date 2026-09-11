import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the continuum Euclidean Yang--Mills spine. -/
structure EuclideanYangMillsCompleteConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  certificate : EuclideanYangMillsCompleteConstructionCertificate S
  limitReady : S.limitReady
  targetReady : S.toUnconditionalTarget.ready
  constructionOutputs :
    S.continuumFourDimensionalYangMillsMeasureConstructed ∧
      S.nontrivialCompactGaugeGroupConstructed ∧
        S.interactingContinuumLimitConstructed ∧
          S.gaugeInvariantSchwingerFunctionsConstructed
  measureStructure :
    S.measurePackage.reflectionPositive ∧
      S.measurePackage.euclideanInvariant ∧
        S.measurePackage.symmetric ∧
          S.measurePackage.clusterProperty ∧
            S.measurePackage.regularity
  gaugeGroupStructure :
    S.measurePackage.gaugeGroupCompact ∧
      S.measurePackage.gaugeGroupNontrivial

namespace EuclideanYangMillsCompleteConstructionClosure

/-- Build the construction-only closure from the continuum construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsCompleteConstructionClosure S :=
  let C := EuclideanYangMillsCompleteConstructionCertificate.ofSpine S
  { certificate := C
    limitReady := C.limitReady
    targetReady := C.targetReady
    constructionOutputs :=
      EuclideanYangMillsCompleteConstructionCertificate.completeConstructionOutputs C
    measureStructure :=
      EuclideanYangMillsCompleteConstructionCertificate.completeMeasureStructure C
    gaugeGroupStructure :=
      EuclideanYangMillsCompleteConstructionCertificate.completeGaugeGroupStructure C }

/-- Extract the continuum four-dimensional Euclidean Yang--Mills measure
construction from the closure. -/
theorem continuumMeasureConstructed
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    S.continuumFourDimensionalYangMillsMeasureConstructed :=
  K.constructionOutputs.1

/-- Extract the nontrivial compact gauge-group construction from the closure. -/
theorem nontrivialCompactGaugeGroupConstructed
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    S.nontrivialCompactGaugeGroupConstructed :=
  K.constructionOutputs.2.1

/-- Extract the interacting continuum-limit construction from the closure. -/
theorem interactingContinuumLimitConstructed
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    S.interactingContinuumLimitConstructed :=
  K.constructionOutputs.2.2.1

/-- Extract the gauge-invariant Schwinger-function construction from the closure. -/
theorem gaugeInvariantSchwingerFunctionsConstructed
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    S.gaugeInvariantSchwingerFunctionsConstructed :=
  K.constructionOutputs.2.2.2

/-- The construction spine has a construction-only closure. -/
theorem nonempty_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty (EuclideanYangMillsCompleteConstructionClosure S) :=
  ⟨ofSpine S⟩

end EuclideanYangMillsCompleteConstructionClosure

end

end MathlibAnalytic
end MGAP4D
