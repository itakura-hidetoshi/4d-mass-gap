import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeActionModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4GaugeActionModel

/-- Bundled construction outputs for the R4 gauge-transformation/action layer. -/
def actionOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (A : EuclideanYangMillsR4GaugeActionModel S K R4) : Prop :=
  A.gaugeTransformations = R4.model.gaugeGroup ∧
    A.actionDomain = R4.model.gaugeFieldConfiguration ∧
      A.gaugeActionConstructed ∧
        A.actionRespectsR4Carrier ∧
          A.actionRespectsGaugeFieldCarrier ∧
            S.gaugeInvariantSchwingerFunctionsConstructed ∧
              S.measurePackage.euclideanInvariant

/-- The R4 gauge-action model proves its bundled construction outputs. -/
theorem actionOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (A : EuclideanYangMillsR4GaugeActionModel S K R4) :
    A.actionOutputs :=
  ⟨A.gaugeTransformations_eq_gaugeGroup,
    ⟨A.actionDomain_eq_configuration,
      ⟨A.gaugeActionConstructed_proof,
        ⟨A.actionRespectsR4Carrier_proof,
          ⟨A.actionRespectsGaugeFieldCarrier_proof,
            ⟨A.gaugeInvariantSchwingerFunctionsConstructed,
              A.euclideanInvariant⟩⟩⟩⟩⟩⟩

/-- The R4 gauge-field construction closure induces an R4 gauge-action model. -/
theorem nonempty_ofR4ConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    Nonempty (EuclideanYangMillsR4GaugeActionModel S K R4) :=
  ⟨ofR4ConstructionClosure S K R4⟩

/-- The R4 gauge-field construction closure proves the bundled gauge-action
construction outputs. -/
theorem actionOutputs_ofR4ConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    (ofR4ConstructionClosure S K R4).actionOutputs :=
  actionOutputs_holds (ofR4ConstructionClosure S K R4)

/-- The continuum construction spine induces a gauge-action model over its R4
gauge-field closure. -/
theorem nonempty_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty
      (EuclideanYangMillsR4GaugeActionModel S
        (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
        (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)) :=
  ⟨ofR4ConstructionClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)⟩

end EuclideanYangMillsR4GaugeActionModel

end

end MathlibAnalytic
end MGAP4D
