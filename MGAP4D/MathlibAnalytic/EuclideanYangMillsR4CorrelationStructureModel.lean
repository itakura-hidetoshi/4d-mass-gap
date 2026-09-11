import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4CorrelationFunctionalClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

structure EuclideanYangMillsR4CorrelationStructureModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) where
  functionalClosure : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N
  functionalClosure_eq : functionalClosure = F
  correlationCarrier : ℕ → Type
  correlationCarrier_eq_functional :
    correlationCarrier = F.functionalModel.correlationFunctionalCarrier
  observableCarrier : Type
  observableCarrier_eq_functional : observableCarrier = F.functionalModel.observableCarrier
  orbitCarrier : Type
  orbitCarrier_eq_functional : orbitCarrier = F.functionalModel.orbitCarrier
  gaugeInvariantPreserved : G.orbitModel.gaugeInvariantConstruction
  euclideanInvariantPreserved : G.orbitModel.euclideanInvariantConstruction
  reflectionPositivePreserved : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4CorrelationStructureModel

def ofCorrelationFunctionalClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) :
    EuclideanYangMillsR4CorrelationStructureModel S K R4 A G H N F :=
  { functionalClosure := F
    functionalClosure_eq := rfl
    correlationCarrier := F.functionalModel.correlationFunctionalCarrier
    correlationCarrier_eq_functional := rfl
    observableCarrier := F.functionalModel.observableCarrier
    observableCarrier_eq_functional := rfl
    orbitCarrier := F.functionalModel.orbitCarrier
    orbitCarrier_eq_functional := rfl
    gaugeInvariantPreserved := F.gaugeInvariantEvidence
    euclideanInvariantPreserved := F.euclideanInvariantEvidence
    reflectionPositivePreserved := F.reflectionPositive }

theorem correlationCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    (M : EuclideanYangMillsR4CorrelationStructureModel S K R4 A G H N F) :
    M.correlationCarrier = F.functionalModel.correlationFunctionalCarrier :=
  M.correlationCarrier_eq_functional

end EuclideanYangMillsR4CorrelationStructureModel

end

end MathlibAnalytic
end MGAP4D
