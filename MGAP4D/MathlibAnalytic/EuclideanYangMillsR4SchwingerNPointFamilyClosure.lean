import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4SchwingerNPointFamilyTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the R4 Schwinger n-point family layer. -/
structure EuclideanYangMillsR4SchwingerNPointFamilyClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) where
  familyModel : EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H
  familyOutputs : familyModel.nPointFamilyOutputs
  nPointFamilyCarrier : familyModel.nPointFamily = H.schwingerModel.schwingerFunctions
  observableCarrier : familyModel.observableCarrier = H.schwingerModel.observableCarrier
  orbitCarrier : familyModel.orbitCarrier = H.schwingerModel.orbitCarrier
  gaugeInvariantEvidence : G.orbitModel.gaugeInvariantConstruction
  euclideanInvariantEvidence : G.orbitModel.euclideanInvariantConstruction
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4SchwingerNPointFamilyClosure

/-- Build the R4 Schwinger n-point family closure from the gauge-invariant
Schwinger closure. -/
def ofSchwingerClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H :=
  let N := EuclideanYangMillsR4SchwingerNPointFamilyModel.ofSchwingerClosure S K R4 A G H
  { familyModel := N
    familyOutputs :=
      EuclideanYangMillsR4SchwingerNPointFamilyModel.nPointFamilyOutputs_holds N
    nPointFamilyCarrier := N.nPointFamily_eq_schwingerFunctions
    observableCarrier := N.observableCarrier_eq_model
    orbitCarrier := N.orbitCarrier_eq_model
    gaugeInvariantEvidence := N.gaugeInvariantEvidence
    euclideanInvariantEvidence := N.euclideanInvariantEvidence
    reflectionPositive := N.reflectionPositive }

/-- Build the R4 Schwinger n-point family closure directly from the continuum
construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4SchwingerNPointFamilyClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S) :=
  ofSchwingerClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)

/-- Extract the n-point family carrier. -/
theorem nPointFamilyCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (C : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) :
    C.familyModel.nPointFamily = H.schwingerModel.schwingerFunctions :=
  C.nPointFamilyCarrier

/-- Extract the bundled n-point family outputs. -/
theorem nPointFamilyOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (C : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H) :
    C.familyModel.nPointFamilyOutputs :=
  C.familyOutputs

end EuclideanYangMillsR4SchwingerNPointFamilyClosure

end

end MathlibAnalytic
end MGAP4D
