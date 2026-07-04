import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeInvariantSchwingerClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only model for the R4 gauge-invariant Schwinger n-point family. -/
structure EuclideanYangMillsR4SchwingerNPointFamilyModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) where
  schwingerClosure : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G
  schwingerClosure_eq : schwingerClosure = H
  nPointFamily : ℕ → Type
  nPointFamily_eq_schwingerFunctions :
    nPointFamily = H.schwingerModel.schwingerFunctions
  observableCarrier : Type
  observableCarrier_eq_model : observableCarrier = H.schwingerModel.observableCarrier
  orbitCarrier : Type
  orbitCarrier_eq_model : orbitCarrier = H.schwingerModel.orbitCarrier
  gaugeInvariantEvidence : H.schwingerModel.gaugeInvariantSchwingerFunctionsConstructed
  euclideanInvariantEvidence : H.schwingerModel.euclideanInvariant
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4SchwingerNPointFamilyModel

/-- Build the R4 Schwinger n-point family model from the gauge-invariant
Schwinger closure. -/
def ofSchwingerClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H :=
  { schwingerClosure := H
    schwingerClosure_eq := rfl
    nPointFamily := H.schwingerModel.schwingerFunctions
    nPointFamily_eq_schwingerFunctions := rfl
    observableCarrier := H.schwingerModel.observableCarrier
    observableCarrier_eq_model := rfl
    orbitCarrier := H.schwingerModel.orbitCarrier
    orbitCarrier_eq_model := rfl
    gaugeInvariantEvidence := H.schwingerModel.gaugeInvariantSchwingerFunctionsConstructed
    euclideanInvariantEvidence := H.schwingerModel.euclideanInvariant
    reflectionPositive := H.reflectionPositive }

/-- Extract the n-point family carrier. -/
theorem nPointFamilyCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (N : EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H) :
    N.nPointFamily = H.schwingerModel.schwingerFunctions :=
  N.nPointFamily_eq_schwingerFunctions

/-- Extract the observable carrier. -/
theorem observableCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (N : EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H) :
    N.observableCarrier = H.schwingerModel.observableCarrier :=
  N.observableCarrier_eq_model

/-- Extract the orbit carrier. -/
theorem orbitCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (N : EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H) :
    N.orbitCarrier = H.schwingerModel.orbitCarrier :=
  N.orbitCarrier_eq_model

end EuclideanYangMillsR4SchwingerNPointFamilyModel

end

end MathlibAnalytic
end MGAP4D
