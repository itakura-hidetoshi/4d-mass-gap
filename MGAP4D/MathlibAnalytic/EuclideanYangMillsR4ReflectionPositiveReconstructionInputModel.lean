import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4CorrelationStructureClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F) where
  correlationStructure : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F
  correlationStructure_eq : correlationStructure = C
  reconstructionInputCarrier : ℕ → Type
  reconstructionInputCarrier_eq_correlation :
    reconstructionInputCarrier = C.structureModel.correlationCarrier
  observableCarrier : Type
  observableCarrier_eq_structure : observableCarrier = C.structureModel.observableCarrier
  orbitCarrier : Type
  orbitCarrier_eq_structure : orbitCarrier = C.structureModel.orbitCarrier
  reflectionPositiveInput : S.measurePackage.reflectionPositive
  euclideanInvariantInput : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariantInput : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel

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
    EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel S K R4 A G H N F C :=
  { correlationStructure := C
    correlationStructure_eq := rfl
    reconstructionInputCarrier := C.structureModel.correlationCarrier
    reconstructionInputCarrier_eq_correlation := rfl
    observableCarrier := C.structureModel.observableCarrier
    observableCarrier_eq_structure := rfl
    orbitCarrier := C.structureModel.orbitCarrier
    orbitCarrier_eq_structure := rfl
    reflectionPositiveInput := C.reflectionPositivePreserved
    euclideanInvariantInput := C.euclideanInvariantPreserved
    gaugeInvariantInput := C.gaugeInvariantPreserved }

theorem reconstructionInputCarrier_eq
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
    M.reconstructionInputCarrier = C.structureModel.correlationCarrier :=
  M.reconstructionInputCarrier_eq_correlation

end EuclideanYangMillsR4ReflectionPositiveReconstructionInputModel

end

end MathlibAnalytic
end MGAP4D
