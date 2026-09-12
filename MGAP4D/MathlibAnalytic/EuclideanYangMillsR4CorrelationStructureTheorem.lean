import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4CorrelationStructureModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4CorrelationStructureModel

def structureOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    (M : EuclideanYangMillsR4CorrelationStructureModel S K R4 A G H N F) : Prop :=
  M.correlationCarrier = F.functionalModel.correlationFunctionalCarrier ∧
    M.observableCarrier = F.functionalModel.observableCarrier ∧
      M.orbitCarrier = F.functionalModel.orbitCarrier ∧
        G.orbitModel.gaugeInvariantConstruction ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            S.measurePackage.reflectionPositive

theorem structureOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    (M : EuclideanYangMillsR4CorrelationStructureModel S K R4 A G H N F) :
    M.structureOutputs :=
  ⟨M.correlationCarrier_eq_functional,
    M.observableCarrier_eq_functional,
    M.orbitCarrier_eq_functional,
    M.gaugeInvariantPreserved,
    M.euclideanInvariantPreserved,
    M.reflectionPositivePreserved⟩

theorem nonempty_ofCorrelationFunctionalClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) :
    Nonempty (EuclideanYangMillsR4CorrelationStructureModel S K R4 A G H N F) :=
  ⟨ofCorrelationFunctionalClosure S K R4 A G H N F⟩

end EuclideanYangMillsR4CorrelationStructureModel

end

end MathlibAnalytic
end MGAP4D
