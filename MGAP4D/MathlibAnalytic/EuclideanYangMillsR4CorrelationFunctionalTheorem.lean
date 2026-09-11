import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4CorrelationFunctionalModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4CorrelationFunctionalModel

/-- Bundled construction outputs for the R4 correlation functional layer. -/
def correlationFunctionalOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (F : EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N) : Prop :=
  F.correlationFunctionalCarrier = N.familyModel.nPointFamily ∧
    F.observableCarrier = N.familyModel.observableCarrier ∧
      F.orbitCarrier = N.familyModel.orbitCarrier ∧
        G.orbitModel.gaugeInvariantConstruction ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            S.measurePackage.reflectionPositive

/-- The R4 correlation functional model proves its bundled outputs. -/
theorem correlationFunctionalOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (F : EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N) :
    F.correlationFunctionalOutputs :=
  ⟨F.correlationFunctionalCarrier_eq_nPointFamily,
    F.observableCarrier_eq_family,
    F.orbitCarrier_eq_family,
    F.gaugeInvariantEvidence,
    F.euclideanInvariantEvidence,
    F.reflectionPositive⟩

/-- The n-point family closure induces the R4 correlation functional model. -/
theorem nonempty_ofNPointFamilyClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) :
    Nonempty (EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N) :=
  ⟨ofNPointFamilyClosure S K R4 A G H N⟩

/-- The n-point family closure proves the bundled R4 correlation functional
outputs. -/
theorem correlationFunctionalOutputs_ofNPointFamilyClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) :
    (ofNPointFamilyClosure S K R4 A G H N).correlationFunctionalOutputs :=
  correlationFunctionalOutputs_holds (ofNPointFamilyClosure S K R4 A G H N)

end EuclideanYangMillsR4CorrelationFunctionalModel

end

end MathlibAnalytic
end MGAP4D
