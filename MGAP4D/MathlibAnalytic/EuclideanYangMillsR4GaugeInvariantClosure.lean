import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeOrbitTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the R4 gauge-orbit and gauge-invariant layer. -/
structure EuclideanYangMillsR4GaugeInvariantClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4) where
  orbitModel : EuclideanYangMillsR4GaugeOrbitModel S K R4 A
  orbitOutputs : orbitModel.orbitOutputs
  orbitCarrier_actionDomain : orbitModel.orbitCarrier = A.actionModel.actionDomain
  orbitCarrier_configuration : orbitModel.orbitCarrier = R4.model.gaugeFieldConfiguration
  gaugeInvariantConstruction : orbitModel.gaugeInvariantConstruction
  euclideanInvariantConstruction : orbitModel.euclideanInvariantConstruction
  compactNontrivialGaugeGroup :
    S.measurePackage.gaugeGroupCompact ∧ S.measurePackage.gaugeGroupNontrivial

namespace EuclideanYangMillsR4GaugeInvariantClosure

/-- Build the R4 gauge-invariant closure from the R4 gauge-action closure. -/
def ofGaugeActionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    EuclideanYangMillsR4GaugeInvariantClosure S K R4 A :=
  let O := EuclideanYangMillsR4GaugeOrbitModel.ofGaugeActionClosure S K R4 A
  { orbitModel := O
    orbitOutputs := EuclideanYangMillsR4GaugeOrbitModel.orbitOutputs_holds O
    orbitCarrier_actionDomain := O.orbitCarrier_eq_actionDomain
    orbitCarrier_configuration := O.orbitCarrier_eq_configuration
    gaugeInvariantConstruction := O.gaugeInvariantConstruction_proof
    euclideanInvariantConstruction := O.euclideanInvariantConstruction_proof
    compactNontrivialGaugeGroup := O.compactNontrivialGaugeGroup }

/-- Build the R4 gauge-invariant closure directly from the continuum construction
spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4GaugeInvariantClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S) :=
  ofGaugeActionClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)

/-- Extract the orbit carrier as the action domain. -/
theorem orbitCarrier_actionDomain_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (C : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    C.orbitModel.orbitCarrier = A.actionModel.actionDomain :=
  C.orbitCarrier_actionDomain

/-- Extract the orbit carrier as the R4 gauge-field configuration carrier. -/
theorem orbitCarrier_configuration_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (C : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    C.orbitModel.orbitCarrier = R4.model.gaugeFieldConfiguration :=
  C.orbitCarrier_configuration

/-- Extract the gauge-invariant construction evidence. -/
theorem gaugeInvariantConstruction_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (C : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    C.orbitModel.gaugeInvariantConstruction :=
  C.gaugeInvariantConstruction

end EuclideanYangMillsR4GaugeInvariantClosure

end

end MathlibAnalytic
end MGAP4D
