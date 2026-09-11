import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel

def reconstructionInputOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    (M : EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel S K R4 A G H N F C) : Prop :=
  M.reconstructionInputCarrier = C.structureModel.correlationCarrier ∧
    M.observableCarrier = C.structureModel.observableCarrier ∧
      M.orbitCarrier = C.structureModel.orbitCarrier ∧
        S.measurePackage.reflectionPositive ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            G.orbitModel.gaugeInvariantConstruction

theorem reconstructionInputOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    (M : EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel S K R4 A G H N F C) :
    M.reconstructionInputOutputs :=
  ⟨M.reconstructionInputCarrier_eq_correlation,
    M.observableCarrier_eq_structure,
    M.orbitCarrier_eq_structure,
    M.reflectionPositiveInput,
    M.euclideanInvariantInput,
    M.gaugeInvariantInput⟩

theorem nonempty_ofCorrelationStructureClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F) :
    Nonempty (EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel S K R4 A G H N F C) :=
  ⟨ofCorrelationStructureClosure S K R4 A G H N F C⟩

end EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel

end

end MathlibAnalytic
end MGAP4D
