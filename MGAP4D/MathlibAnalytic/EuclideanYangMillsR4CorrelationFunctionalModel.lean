import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4SchwingerNPointFamilyClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only carrier for the R4 Schwinger correlation functional layer. -/
structure EuclideanYangMillsR4CorrelationFunctionalModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) where
  nPointFamilyClosure : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H
  nPointFamilyClosure_eq : nPointFamilyClosure = N
  correlationFunctionalCarrier : ℕ → Type
  correlationFunctionalCarrier_eq_nPointFamily :
    correlationFunctionalCarrier = N.familyModel.nPointFamily
  observableCarrier : Type
  observableCarrier_eq_family : observableCarrier = N.familyModel.observableCarrier
  orbitCarrier : Type
  orbitCarrier_eq_family : orbitCarrier = N.familyModel.orbitCarrier
  gaugeInvariantEvidence : G.orbitModel.gaugeInvariantConstruction
  euclideanInvariantEvidence : G.orbitModel.euclideanInvariantConstruction
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4CorrelationFunctionalModel

/-- Build the R4 correlation functional model from the n-point family closure. -/
def ofNPointFamilyClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) :
    EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N :=
  { nPointFamilyClosure := N
    nPointFamilyClosure_eq := rfl
    correlationFunctionalCarrier := N.familyModel.nPointFamily
    correlationFunctionalCarrier_eq_nPointFamily := rfl
    observableCarrier := N.familyModel.observableCarrier
    observableCarrier_eq_family := rfl
    orbitCarrier := N.familyModel.orbitCarrier
    orbitCarrier_eq_family := rfl
    gaugeInvariantEvidence := N.gaugeInvariantEvidence
    euclideanInvariantEvidence := N.euclideanInvariantEvidence
    reflectionPositive := N.reflectionPositive }

/-- Extract the correlation functional carrier. -/
theorem correlationFunctionalCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (F : EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N) :
    F.correlationFunctionalCarrier = N.familyModel.nPointFamily :=
  F.correlationFunctionalCarrier_eq_nPointFamily

/-- Extract the observable carrier. -/
theorem observableCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (F : EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N) :
    F.observableCarrier = N.familyModel.observableCarrier :=
  F.observableCarrier_eq_family

/-- Extract the orbit carrier. -/
theorem orbitCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (F : EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N) :
    F.orbitCarrier = N.familyModel.orbitCarrier :=
  F.orbitCarrier_eq_family

end EuclideanYangMillsR4CorrelationFunctionalModel

end

end MathlibAnalytic
end MGAP4D
