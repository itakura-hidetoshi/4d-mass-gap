import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeFieldConstructionTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the R4 Euclidean Yang--Mills gauge-field model. -/
structure EuclideanYangMillsR4GaugeFieldConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S) where
  model : EuclideanYangMillsR4GaugeFieldModel S K
  constructionOutputs : model.constructionOutputs
  spacetimeR4 : model.spacetime = EuclideanSpacetimeR4
  gaugeFieldConfigurationCarrier :
    model.gaugeFieldConfiguration = S.measurePackage.configurationSpace
  gaugeGroupCarrier : model.gaugeGroup = S.measurePackage.gaugeGroup
  fieldAlgebraCarrier : model.fieldAlgebra = S.measurePackage.fieldAlgebra
  schwingerFunctionsCarrier :
    model.schwingerFunctions = S.measurePackage.schwingerFunctions

namespace EuclideanYangMillsR4GaugeFieldConstructionClosure

/-- Build the R4 gauge-field construction closure from a construction-only
Yang--Mills closure. -/
def ofConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S) :
    EuclideanYangMillsR4GaugeFieldConstructionClosure S K :=
  let M := EuclideanYangMillsR4GaugeFieldModel.ofConstructionClosure S K
  { model := M
    constructionOutputs :=
      EuclideanYangMillsR4GaugeFieldModel.constructionOutputs_holds M
    spacetimeR4 := M.spacetime_eq_r4
    gaugeFieldConfigurationCarrier := M.gaugeFieldConfiguration_eq_measurePackage
    gaugeGroupCarrier := M.gaugeGroup_eq_measurePackage
    fieldAlgebraCarrier := M.fieldAlgebra_eq_measurePackage
    schwingerFunctionsCarrier := M.schwingerFunctions_eq_measurePackage }

/-- Build the R4 gauge-field construction closure directly from the continuum
construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4GaugeFieldConstructionClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S) :=
  ofConstructionClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)

/-- Extract the R4 spacetime carrier statement. -/
theorem spacetimeCarrier
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (C : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    C.model.spacetime = EuclideanSpacetimeR4 :=
  C.spacetimeR4

/-- Extract the gauge-field configuration carrier statement. -/
theorem gaugeFieldConfigurationCarrier
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (C : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    C.model.gaugeFieldConfiguration = S.measurePackage.configurationSpace :=
  C.gaugeFieldConfigurationCarrier

/-- Extract the complete R4 gauge-field construction outputs. -/
theorem constructionOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    (C : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    C.model.constructionOutputs :=
  C.constructionOutputs

end EuclideanYangMillsR4GaugeFieldConstructionClosure

end

end MathlibAnalytic
end MGAP4D
