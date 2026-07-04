import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeInvariantSchwingerModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4GaugeInvariantSchwingerModel

/-- Bundled construction outputs for the R4 gauge-invariant Schwinger-function
layer. -/
def schwingerOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (M : EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G) : Prop :=
  M.orbitCarrier = G.orbitModel.orbitCarrier ∧
    M.observableCarrier = R4.model.fieldAlgebra ∧
      M.schwingerFunctions = S.measurePackage.schwingerFunctions ∧
        S.gaugeInvariantSchwingerFunctionsConstructed ∧
          S.measurePackage.euclideanInvariant ∧
            S.measurePackage.reflectionPositive

/-- The R4 gauge-invariant Schwinger-function model proves its bundled outputs. -/
theorem schwingerOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (M : EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G) :
    M.schwingerOutputs :=
  ⟨M.orbitCarrier_eq_closure,
    M.observableCarrier_eq_fieldAlgebra,
    M.schwingerFunctions_eq_measurePackage,
    M.gaugeInvariantSchwingerFunctionsConstructed,
    M.euclideanInvariant,
    M.reflectionPositive⟩

/-- The R4 gauge-invariant closure induces a gauge-invariant Schwinger-function
model. -/
theorem nonempty_ofGaugeInvariantClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    Nonempty (EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G) :=
  ⟨ofGaugeInvariantClosure S K R4 A G⟩

/-- The R4 gauge-invariant closure proves the bundled Schwinger-function outputs. -/
theorem schwingerOutputs_ofGaugeInvariantClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    (ofGaugeInvariantClosure S K R4 A G).schwingerOutputs :=
  schwingerOutputs_holds (ofGaugeInvariantClosure S K R4 A G)

/-- The continuum construction spine induces the R4 gauge-invariant
Schwinger-function model over its closure. -/
theorem nonempty_ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    Nonempty
      (EuclideanYangMillsR4GaugeInvariantSchwingerModel S
        (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
        (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
        (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
        (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)) :=
  ⟨ofGaugeInvariantClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)⟩

end EuclideanYangMillsR4GaugeInvariantSchwingerModel

end

end MathlibAnalytic
end MGAP4D
