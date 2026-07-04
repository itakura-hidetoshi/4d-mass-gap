import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeOrbitModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4GaugeOrbitModel

/-- Bundled construction outputs for the R4 gauge-orbit layer. -/
def orbitOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (O : EuclideanYangMillsR4GaugeOrbitModel S K R4 A) : Prop :=
  O.orbitCarrier = A.actionModel.actionDomain ∧
    O.orbitCarrier = R4.model.gaugeFieldConfiguration ∧
      O.gaugeInvariantConstruction ∧
        O.euclideanInvariantConstruction ∧
          S.measurePackage.gaugeGroupCompact ∧
            S.measurePackage.gaugeGroupNontrivial

/-- The R4 gauge-orbit model proves its bundled construction outputs. -/
theorem orbitOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    (O : EuclideanYangMillsR4GaugeOrbitModel S K R4 A) :
    O.orbitOutputs :=
  ⟨O.orbitCarrier_eq_actionDomain,
    O.orbitCarrier_eq_configuration,
    O.gaugeInvariantConstruction_proof,
    O.euclideanInvariantConstruction_proof,
    O.compactNontrivialGaugeGroup.1,
    O.compactNontrivialGaugeGroup.2⟩

/-- The R4 gauge-action closure induces a gauge-orbit model. -/
theorem nonempty_ofGaugeActionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    Nonempty (EuclideanYangMillsR4GaugeOrbitModel S K R4 A) :=
  ⟨ofGaugeActionClosure S K R4 A⟩

/-- The R4 gauge-action closure proves the bundled orbit outputs. -/
theorem orbitOutputs_ofGaugeActionClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4) :
    (ofGaugeActionClosure S K R4 A).orbitOutputs :=
  orbitOutputs_holds (ofGaugeActionClosure S K R4 A)

/-- The continuum construction spine induces a gauge-orbit model over its R4
gauge-action closure. -/
theorem nonempty_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty
      (EuclideanYangMillsR4GaugeOrbitModel S
        (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
        (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
        (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)) :=
  ⟨ofGaugeActionClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)⟩

end EuclideanYangMillsR4GaugeOrbitModel

end

end MathlibAnalytic
end MGAP4D
