import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeActionClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only gauge-orbit model over the R4 gauge-action closure.

This layer does not quotient by gauge equivalence as a new analytic construction.
It records the orbit carrier and invariance evidence available from the completed
R4 gauge-action construction: the orbit carrier is the action domain, and the
invariance evidence is the construction-side gauge-invariant Schwinger-function
and Euclidean-invariance output. -/
structure EuclideanYangMillsR4GaugeOrbitModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4) where
  actionClosure : EuclideanYangMillsR4GaugeActionClosure S K R4
  actionClosure_eq : actionClosure = A
  orbitCarrier : Type
  orbitCarrier_eq_actionDomain : orbitCarrier = A.actionModel.actionDomain
  orbitCarrier_eq_configuration : orbitCarrier = R4.model.gaugeFieldConfiguration
  gaugeInvariantConstruction : Prop
  gaugeInvariantConstruction_proof : gaugeInvariantConstruction
  euclideanInvariantConstruction : Prop
  euclideanInvariantConstruction_proof : euclideanInvariantConstruction
  compactNontrivialGaugeGroup :
    S.measurePackage.gaugeGroupCompact ∧ S.measurePackage.gaugeGroupNontrivial

namespace EuclideanYangMillsR4GaugeOrbitModel

/-- Build the gauge-orbit model from the R4 gauge-action closure. -/
def ofGaugeActionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    EuclideanYangMillsR4GaugeOrbitModel S K R4 A :=
  { actionClosure := A
    actionClosure_eq := rfl
    orbitCarrier := A.actionModel.actionDomain
    orbitCarrier_eq_actionDomain := rfl
    orbitCarrier_eq_configuration := A.actionDomainCarrier
    gaugeInvariantConstruction := S.gaugeInvariantSchwingerFunctionsConstructed
    gaugeInvariantConstruction_proof := A.gaugeInvariantSchwingerFunctionsConstructed
    euclideanInvariantConstruction := S.measurePackage.euclideanInvariant
    euclideanInvariantConstruction_proof := A.euclideanInvariant
    compactNontrivialGaugeGroup :=
      EuclideanYangMillsR4GaugeFieldModel.compactNontrivialGaugeGroup R4.model }

/-- Extract the orbit carrier as the action domain. -/
theorem orbitCarrier_actionDomain
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (O : EuclideanYangMillsR4GaugeOrbitModel S K R4 A) :
    O.orbitCarrier = A.actionModel.actionDomain :=
  O.orbitCarrier_eq_actionDomain

/-- Extract the orbit carrier as the R4 gauge-field configuration carrier. -/
theorem orbitCarrier_configuration
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (O : EuclideanYangMillsR4GaugeOrbitModel S K R4 A) :
    O.orbitCarrier = R4.model.gaugeFieldConfiguration :=
  O.orbitCarrier_eq_configuration

/-- Extract the gauge-invariant construction evidence. -/
theorem gaugeInvariantConstruction_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (O : EuclideanYangMillsR4GaugeOrbitModel S K R4 A) :
    O.gaugeInvariantConstruction :=
  O.gaugeInvariantConstruction_proof

end EuclideanYangMillsR4GaugeOrbitModel

end

end MathlibAnalytic
end MGAP4D
