import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4CorrelationStructureTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsR4CorrelationStructureClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) where
  structureModel : EuclideanYangMillsR4CorrelationStructureModel S K R4 A G H N F
  structureOutputs : structureModel.structureOutputs
  correlationCarrier :
    structureModel.correlationCarrier = F.functionalModel.correlationFunctionalCarrier
  observableCarrier : structureModel.observableCarrier = F.functionalModel.observableCarrier
  orbitCarrier : structureModel.orbitCarrier = F.functionalModel.orbitCarrier
  gaugeInvariantPreserved : G.orbitModel.gaugeInvariantConstruction
  euclideanInvariantPreserved : G.orbitModel.euclideanInvariantConstruction
  reflectionPositivePreserved : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4CorrelationStructureClosure

def ofCorrelationFunctionalClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) :
    EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F :=
  let M := EuclideanYangMillsR4CorrelationStructureModel.ofCorrelationFunctionalClosure S K R4 A G H N F
  { structureModel := M
    structureOutputs := EuclideanYangMillsR4CorrelationStructureModel.structureOutputs_holds M
    correlationCarrier := M.correlationCarrier_eq_functional
    observableCarrier := M.observableCarrier_eq_functional
    orbitCarrier := M.orbitCarrier_eq_functional
    gaugeInvariantPreserved := M.gaugeInvariantPreserved
    euclideanInvariantPreserved := M.euclideanInvariantPreserved
    reflectionPositivePreserved := M.reflectionPositivePreserved }

def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4CorrelationStructureClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
      (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S) :=
  ofCorrelationFunctionalClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
    (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)

theorem structureOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F) :
    C.structureModel.structureOutputs :=
  C.structureOutputs

end EuclideanYangMillsR4CorrelationStructureClosure

end

end MathlibAnalytic
end MGAP4D
