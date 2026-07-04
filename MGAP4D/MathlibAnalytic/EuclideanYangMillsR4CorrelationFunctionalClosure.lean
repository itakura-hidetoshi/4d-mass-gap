import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4CorrelationFunctionalTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the R4 correlation functional layer. -/
structure EuclideanYangMillsR4CorrelationFunctionalClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) where
  functionalModel : EuclideanYangMillsR4CorrelationFunctionalModel S K R4 A G H N
  functionalOutputs : functionalModel.correlationFunctionalOutputs
  correlationFunctionalCarrier :
    functionalModel.correlationFunctionalCarrier = N.familyModel.nPointFamily
  observableCarrier : functionalModel.observableCarrier = N.familyModel.observableCarrier
  orbitCarrier : functionalModel.orbitCarrier = N.familyModel.orbitCarrier
  gaugeInvariantEvidence : G.orbitModel.gaugeInvariantConstruction
  euclideanInvariantEvidence : G.orbitModel.euclideanInvariantConstruction
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4CorrelationFunctionalClosure

/-- Build the R4 correlation functional closure from the n-point family closure. -/
def ofNPointFamilyClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) :
    EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N :=
  let F := EuclideanYangMillsR4CorrelationFunctionalModel.ofNPointFamilyClosure S K R4 A G H N
  { functionalModel := F
    functionalOutputs :=
      EuclideanYangMillsR4CorrelationFunctionalModel.correlationFunctionalOutputs_holds F
    correlationFunctionalCarrier := F.correlationFunctionalCarrier_eq_nPointFamily
    observableCarrier := F.observableCarrier_eq_family
    orbitCarrier := F.orbitCarrier_eq_family
    gaugeInvariantEvidence := F.gaugeInvariantEvidence
    euclideanInvariantEvidence := F.euclideanInvariantEvidence
    reflectionPositive := F.reflectionPositive }

/-- Build the R4 correlation functional closure directly from the continuum
construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4CorrelationFunctionalClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
      (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S) :=
  ofNPointFamilyClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
    (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)

/-- Extract the correlation functional carrier. -/
theorem correlationFunctionalCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (C : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) :
    C.functionalModel.correlationFunctionalCarrier = N.familyModel.nPointFamily :=
  C.correlationFunctionalCarrier

/-- Extract the bundled correlation functional outputs. -/
theorem correlationFunctionalOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    (C : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N) :
    C.functionalModel.correlationFunctionalOutputs :=
  C.functionalOutputs

end EuclideanYangMillsR4CorrelationFunctionalClosure

end

end MathlibAnalytic
end MGAP4D
