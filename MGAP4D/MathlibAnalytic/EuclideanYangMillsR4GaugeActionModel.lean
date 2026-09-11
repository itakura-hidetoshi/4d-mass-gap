import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeFieldConstructionClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only gauge-transformation/action model over the R4 gauge-field
carrier.

The repository does not yet install a concrete smooth gauge-group action.  This
layer therefore records the exact carrier-level action obligations that the R4
construction has reached: transformations are the constructed gauge group, the
action domain is the constructed gauge-field configuration carrier, and the
available action evidence is the construction-side gauge-invariant Schwinger
function theorem together with the R4/configuration carrier identifications. -/
structure EuclideanYangMillsR4GaugeActionModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) where
  gaugeFieldModel : EuclideanYangMillsR4GaugeFieldModel S K
  gaugeFieldModel_eq : gaugeFieldModel = R4.model
  gaugeTransformations : Type
  gaugeTransformations_eq_gaugeGroup : gaugeTransformations = R4.model.gaugeGroup
  actionDomain : Type
  actionDomain_eq_configuration : actionDomain = R4.model.gaugeFieldConfiguration
  gaugeActionConstructed : Prop
  gaugeActionConstructed_proof : gaugeActionConstructed
  actionRespectsR4Carrier : Prop
  actionRespectsR4Carrier_proof : actionRespectsR4Carrier
  actionRespectsGaugeFieldCarrier : Prop
  actionRespectsGaugeFieldCarrier_proof : actionRespectsGaugeFieldCarrier
  gaugeInvariantSchwingerFunctionsConstructed :
    S.gaugeInvariantSchwingerFunctionsConstructed
  euclideanInvariant : S.measurePackage.euclideanInvariant

namespace EuclideanYangMillsR4GaugeActionModel

/-- Build the R4 gauge-action model from the R4 gauge-field construction closure. -/
def ofR4ConstructionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K) :
    EuclideanYangMillsR4GaugeActionModel S K R4 :=
  { gaugeFieldModel := R4.model
    gaugeFieldModel_eq := rfl
    gaugeTransformations := R4.model.gaugeGroup
    gaugeTransformations_eq_gaugeGroup := rfl
    actionDomain := R4.model.gaugeFieldConfiguration
    actionDomain_eq_configuration := rfl
    gaugeActionConstructed := S.gaugeInvariantSchwingerFunctionsConstructed
    gaugeActionConstructed_proof := R4.model.gaugeInvariantSchwingerFunctionsConstructed
    actionRespectsR4Carrier := R4.model.spacetime = EuclideanSpacetimeR4
    actionRespectsR4Carrier_proof := R4.spacetimeR4
    actionRespectsGaugeFieldCarrier :=
      R4.model.gaugeFieldConfiguration = S.measurePackage.configurationSpace
    actionRespectsGaugeFieldCarrier_proof := R4.gaugeFieldConfigurationCarrier
    gaugeInvariantSchwingerFunctionsConstructed :=
      R4.model.gaugeInvariantSchwingerFunctionsConstructed
    euclideanInvariant := R4.model.euclideanInvariant }

/-- Extract the gauge-transformation carrier. -/
theorem gaugeTransformations_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (A : EuclideanYangMillsR4GaugeActionModel S K R4) :
    A.gaugeTransformations = R4.model.gaugeGroup :=
  A.gaugeTransformations_eq_gaugeGroup

/-- Extract the action-domain carrier. -/
theorem actionDomain_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (A : EuclideanYangMillsR4GaugeActionModel S K R4) :
    A.actionDomain = R4.model.gaugeFieldConfiguration :=
  A.actionDomain_eq_configuration

/-- Extract the construction-side gauge-action evidence. -/
theorem gaugeAction
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    (A : EuclideanYangMillsR4GaugeActionModel S K R4) :
    A.gaugeActionConstructed :=
  A.gaugeActionConstructed_proof

end EuclideanYangMillsR4GaugeActionModel

end

end MathlibAnalytic
end MGAP4D
