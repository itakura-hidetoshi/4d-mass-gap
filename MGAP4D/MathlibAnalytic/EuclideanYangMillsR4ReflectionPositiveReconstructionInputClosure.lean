import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4ReflectionPositiveReconstructionInputTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F) where
  inputModel :
    EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel S K R4 A G H N F C
  inputOutputs : inputModel.reconstructionInputOutputs
  reconstructionInputCarrier :
    inputModel.reconstructionInputCarrier = C.structureModel.correlationCarrier
  observableCarrier : inputModel.observableCarrier = C.structureModel.observableCarrier
  orbitCarrier : inputModel.orbitCarrier = C.structureModel.orbitCarrier
  reflectionPositiveInput : S.measurePackage.reflectionPositive
  euclideanInvariantInput : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariantInput : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure

def ofCorrelationStructureClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F) :
    EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C :=
  let M := EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel.ofCorrelationStructureClosure S K R4 A G H N F C
  { inputModel := M
    inputOutputs :=
      EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel.reconstructionInputOutputs_holds M
    reconstructionInputCarrier := M.reconstructionInputCarrier_eq_correlation
    observableCarrier := M.observableCarrier_eq_structure
    orbitCarrier := M.orbitCarrier_eq_structure
    reflectionPositiveInput := M.reflectionPositiveInput
    euclideanInvariantInput := M.euclideanInvariantInput
    gaugeInvariantInput := M.gaugeInvariantInput }

def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
      (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationStructureClosure.ofSpine S) :=
  ofCorrelationStructureClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
    (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationStructureClosure.ofSpine S)

theorem reconstructionInputOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    I.inputModel.reconstructionInputOutputs :=
  I.inputOutputs

end EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure

end

end MathlibAnalytic
end MGAP4D
