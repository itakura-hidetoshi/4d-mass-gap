import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeInvariantSchwingerTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only closure for the R4 gauge-invariant Schwinger-function layer. -/
structure EuclideanYangMillsR4GaugeInvariantSchwingerClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) where
  schwingerModel : EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G
  schwingerOutputs : schwingerModel.schwingerOutputs
  orbitCarrier : schwingerModel.orbitCarrier = G.orbitModel.orbitCarrier
  observableCarrier : schwingerModel.observableCarrier = R4.model.fieldAlgebra
  schwingerFunctionsCarrier :
    schwingerModel.schwingerFunctions = S.measurePackage.schwingerFunctions
  gaugeInvariantSchwingerFunctionsConstructed :
    G.orbitModel.gaugeInvariantConstruction
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4GaugeInvariantSchwingerClosure

/-- Build the R4 gauge-invariant Schwinger-function closure from the R4
gauge-invariant closure. -/
def ofGaugeInvariantClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G :=
  let M := EuclideanYangMillsR4GaugeInvariantSchwingerModel.ofGaugeInvariantClosure S K R4 A G
  { schwingerModel := M
    schwingerOutputs :=
      EuclideanYangMillsR4GaugeInvariantSchwingerModel.schwingerOutputs_holds M
    orbitCarrier := M.orbitCarrier_eq_closure
    observableCarrier := M.observableCarrier_eq_fieldAlgebra
    schwingerFunctionsCarrier := M.schwingerFunctions_eq_measurePackage
    gaugeInvariantSchwingerFunctionsConstructed :=
      M.gaugeInvariantSchwingerFunctionsConstructed
    euclideanInvariant := M.euclideanInvariant
    reflectionPositive := M.reflectionPositive }

/-- Build the R4 gauge-invariant Schwinger-function closure directly from the
continuum construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4GaugeInvariantSchwingerClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S) :=
  ofGaugeInvariantClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)

/-- Extract the Schwinger-function carrier. -/
theorem schwingerFunctionsCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (C : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    C.schwingerModel.schwingerFunctions = S.measurePackage.schwingerFunctions :=
  C.schwingerFunctionsCarrier

/-- Extract the observable carrier. -/
theorem observableCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (C : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    C.schwingerModel.observableCarrier = R4.model.fieldAlgebra :=
  C.observableCarrier

/-- Extract the bundled Schwinger outputs. -/
theorem schwingerOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (C : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    C.schwingerModel.schwingerOutputs :=
  C.schwingerOutputs

end EuclideanYangMillsR4GaugeInvariantSchwingerClosure

end

end MathlibAnalytic
end MGAP4D
