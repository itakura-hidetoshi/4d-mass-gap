import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4GaugeInvariantClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Construction-only model for gauge-invariant Schwinger functions over the R4
Yang--Mills gauge-invariant closure.

This layer does not introduce a mass-gap statement.  It records that the
Schwinger-function carrier and observable carrier are exactly the carriers already
constructed in the Euclidean measure package, and that the gauge-invariant and
Euclidean-invariant construction evidence retained by the preceding closure is
carried forward without changing its type. -/
structure EuclideanYangMillsR4GaugeInvariantSchwingerModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) where
  gaugeInvariantClosure : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A
  gaugeInvariantClosure_eq : gaugeInvariantClosure = G
  orbitCarrier : Type
  orbitCarrier_eq_closure : orbitCarrier = G.orbitModel.orbitCarrier
  observableCarrier : Type
  observableCarrier_eq_fieldAlgebra : observableCarrier = R4.model.fieldAlgebra
  schwingerFunctions : ℕ → Type
  schwingerFunctions_eq_measurePackage :
    schwingerFunctions = S.measurePackage.schwingerFunctions
  gaugeInvariantSchwingerFunctionsConstructed :
    G.orbitModel.gaugeInvariantConstruction
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  reflectionPositive : S.measurePackage.reflectionPositive

namespace EuclideanYangMillsR4GaugeInvariantSchwingerModel

/-- Build the gauge-invariant Schwinger-function model from the R4
gauge-invariant closure. -/
def ofGaugeInvariantClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A) :
    EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G :=
  { gaugeInvariantClosure := G
    gaugeInvariantClosure_eq := rfl
    orbitCarrier := G.orbitModel.orbitCarrier
    orbitCarrier_eq_closure := rfl
    observableCarrier := R4.model.fieldAlgebra
    observableCarrier_eq_fieldAlgebra := rfl
    schwingerFunctions := S.measurePackage.schwingerFunctions
    schwingerFunctions_eq_measurePackage := rfl
    gaugeInvariantSchwingerFunctionsConstructed := G.gaugeInvariantConstruction
    euclideanInvariant := G.euclideanInvariantConstruction
    reflectionPositive := R4.model.reflectionPositive }

/-- Extract the orbit carrier. -/
theorem orbitCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (M : EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G) :
    M.orbitCarrier = G.orbitModel.orbitCarrier :=
  M.orbitCarrier_eq_closure

/-- Extract the observable carrier. -/
theorem observableCarrier_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (M : EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G) :
    M.observableCarrier = R4.model.fieldAlgebra :=
  M.observableCarrier_eq_fieldAlgebra

/-- Extract the Schwinger-function carrier. -/
theorem schwingerFunctions_eq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    (M : EuclideanYangMillsR4GaugeInvariantSchwingerModel S K R4 A G) :
    M.schwingerFunctions = S.measurePackage.schwingerFunctions :=
  M.schwingerFunctions_eq_measurePackage

end EuclideanYangMillsR4GaugeInvariantSchwingerModel

end

end MathlibAnalytic
end MGAP4D
