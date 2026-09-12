import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeActionTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the R4 gauge-transformation/action layer. -/
structure EuclideanYangMillsR4GaugeActionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) where
  actionModel : EuclideanYangMillsR4GaugeActionModel S K R4
  actionOutputs : actionModel.actionOutputs
  gaugeTransformationsCarrier : actionModel.gaugeTransformations = R4.model.gaugeGroup
  actionDomainCarrier : actionModel.actionDomain = R4.model.gaugeFieldConfiguration
  actionRespectsR4Carrier : actionModel.actionRespectsR4Carrier
  actionRespectsGaugeFieldCarrier : actionModel.actionRespectsGaugeFieldCarrier
  gaugeInvariantSchwingerFunctionsConstructed :
    S.gaugeInvariantSchwingerFunctionsConstructed
  euclideanInvariant : S.measurePackage.euclideanInvariant

namespace EuclideanYangMillsR4GaugeActionClosure

/-- Build the R4 gauge-action closure from the R4 gauge-field construction closure. -/
def ofR4ConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    EuclideanYangMillsR4GaugeActionClosure S K R4 :=
  let A := EuclideanYangMillsR4GaugeActionModel.ofR4ConstructionClosure S K R4
  { actionModel := A
    actionOutputs := EuclideanYangMillsR4GaugeActionModel.actionOutputs_holds A
    gaugeTransformationsCarrier := A.gaugeTransformations_eq_gaugeGroup
    actionDomainCarrier := A.actionDomain_eq_configuration
    actionRespectsR4Carrier := A.actionRespectsR4Carrier_proof
    actionRespectsGaugeFieldCarrier := A.actionRespectsGaugeFieldCarrier_proof
    gaugeInvariantSchwingerFunctionsConstructed :=
      A.gaugeInvariantSchwingerFunctionsConstructed
    euclideanInvariant := A.euclideanInvariant }

/-- Build the R4 gauge-action closure directly from the continuum construction
spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4GaugeActionClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S) :=
  ofR4ConstructionClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)

/-- Extract the gauge-transformation carrier statement. -/
theorem gaugeTransformationsCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (C : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    C.actionModel.gaugeTransformations = R4.model.gaugeGroup :=
  C.gaugeTransformationsCarrier

/-- Extract the action-domain carrier statement. -/
theorem actionDomainCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (C : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    C.actionModel.actionDomain = R4.model.gaugeFieldConfiguration :=
  C.actionDomainCarrier

/-- Extract the full action-output bundle. -/
theorem actionOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (C : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    C.actionModel.actionOutputs :=
  C.actionOutputs

end EuclideanYangMillsR4GaugeActionClosure

end

end MathlibAnalytic
end MGAP4D
