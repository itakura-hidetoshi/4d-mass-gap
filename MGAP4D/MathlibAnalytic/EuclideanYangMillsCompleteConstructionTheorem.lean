import MGAP4D.MathlibAnalytic.EuclideanYangMillsCompleteConstructionCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsCompleteConstructionCertificate

/-- The complete construction certificate proves the four main construction
outputs together. -/
theorem completeConstructionOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.continuumFourDimensionalYangMillsMeasureConstructed ∧
      S.nontrivialCompactGaugeGroupConstructed ∧
        S.interactingContinuumLimitConstructed ∧
          S.gaugeInvariantSchwingerFunctionsConstructed :=
  ⟨C.continuumMeasureConstructed,
    C.nontrivialCompactGaugeGroupConstructed,
    C.interactingContinuumLimitConstructed,
    C.gaugeInvariantSchwingerFunctionsConstructed⟩

/-- The complete construction certificate proves the structural measure outputs
together. -/
theorem completeMeasureStructure
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.measurePackage.reflectionPositive ∧
      S.measurePackage.euclideanInvariant ∧
        S.measurePackage.symmetric ∧
          S.measurePackage.clusterProperty ∧
            S.measurePackage.regularity :=
  ⟨C.reflectionPositivity,
    C.euclideanInvariance,
    C.symmetry,
    C.clusterProperty,
    C.regularity⟩

/-- The complete construction certificate proves the gauge-group outputs
together. -/
theorem completeGaugeGroupStructure
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (C : EuclideanYangMillsCompleteConstructionCertificate S) :
    S.measurePackage.gaugeGroupCompact ∧
      S.measurePackage.gaugeGroupNontrivial :=
  ⟨C.gaugeGroupCompact, C.gaugeGroupNontrivial⟩

/-- The construction spine itself proves the complete construction certificate. -/
theorem completeConstructionCertificate_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty (EuclideanYangMillsCompleteConstructionCertificate S) :=
  ⟨ofSpine S⟩

/-- The construction spine itself proves all four construction outputs. -/
theorem completeConstructionOutputs_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.continuumFourDimensionalYangMillsMeasureConstructed ∧
      S.nontrivialCompactGaugeGroupConstructed ∧
        S.interactingContinuumLimitConstructed ∧
          S.gaugeInvariantSchwingerFunctionsConstructed :=
  completeConstructionOutputs (ofSpine S)

/-- The construction spine itself proves the measure structural outputs. -/
theorem completeMeasureStructure_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.measurePackage.reflectionPositive ∧
      S.measurePackage.euclideanInvariant ∧
        S.measurePackage.symmetric ∧
          S.measurePackage.clusterProperty ∧
            S.measurePackage.regularity :=
  completeMeasureStructure (ofSpine S)

/-- The construction spine itself proves the compact nontrivial gauge group
outputs. -/
theorem completeGaugeGroupStructure_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    S.measurePackage.gaugeGroupCompact ∧
      S.measurePackage.gaugeGroupNontrivial :=
  completeGaugeGroupStructure (ofSpine S)

end EuclideanYangMillsCompleteConstructionCertificate

end

end MathlibAnalytic
end MGAP4D
