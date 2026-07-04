import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4SchwingerNPointFamilyModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4SchwingerNPointFamilyModel

/-- Bundled construction outputs for the R4 Schwinger n-point family. -/
def nPointFamilyOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (N : EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H) : Prop :=
  N.nPointFamily = H.schwingerModel.schwingerFunctions ∧
    N.observableCarrier = H.schwingerModel.observableCarrier ∧
      N.orbitCarrier = H.schwingerModel.orbitCarrier ∧
        H.schwingerModel.gaugeInvariantSchwingerFunctionsConstructed ∧
          H.schwingerModel.euclideanInvariant ∧
            S.measurePackage.reflectionPositive

/-- The R4 Schwinger n-point family model proves its bundled outputs. -/
theorem nPointFamilyOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    (N : EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H) :
    N.nPointFamilyOutputs :=
  ⟨N.nPointFamily_eq_schwingerFunctions,
    N.observableCarrier_eq_model,
    N.orbitCarrier_eq_model,
    N.gaugeInvariantEvidence,
    N.euclideanInvariantEvidence,
    N.reflectionPositive⟩

/-- The R4 gauge-invariant Schwinger closure induces the n-point family model. -/
theorem nonempty_ofSchwingerClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    Nonempty (EuclideanYangMillsR4SchwingerNPointFamilyModel S K R4 A G H) :=
  ⟨ofSchwingerClosure S K R4 A G H⟩

/-- The R4 gauge-invariant Schwinger closure proves the bundled n-point family
outputs. -/
theorem nPointFamilyOutputs_ofSchwingerClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G) :
    (ofSchwingerClosure S K R4 A G H).nPointFamilyOutputs :=
  nPointFamilyOutputs_holds (ofSchwingerClosure S K R4 A G H)

end EuclideanYangMillsR4SchwingerNPointFamilyModel

end

end MathlibAnalytic
end MGAP4D
