import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotientModel

/-- Bundled outputs for the separated quotient stage. -/
def quotientOutputs
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    {I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C}
    {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientModel S K R4 A G H N F C I O) :
    Prop :=
  EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I =
      Sigma I.inputModel.reconstructionInputCarrier ∧
    Equivalence (EuclideanYangMillsR4HilbertReconstructionQuotient.separationRelation I) ∧
      (Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I) →
        Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I)) ∧
        S.measurePackage.reflectionPositive ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            G.orbitModel.gaugeInvariantConstruction

/-- The quotient model proves its bundled outputs. -/
theorem quotientOutputs_holds
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    {I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C}
    {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientModel S K R4 A G H N F C I O) :
    M.quotientOutputs :=
  ⟨M.inputCarrier_eq,
    M.separationEquivalence,
    M.quotientNonempty,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The Hilbert reconstruction carrier closure induces a separated quotient model. -/
theorem nonempty_ofCarrierClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F)
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I) :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotientModel S K R4 A G H N F C I O) :=
  ⟨ofCarrierClosure S K R4 A G H N F C I O⟩

end EuclideanYangMillsR4HilbertReconstructionQuotientModel

end

end MathlibAnalytic
end MGAP4D
