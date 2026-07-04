import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel

/-- Bundled outputs for the quotient projection stage. -/
def projectionOutputs
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
    {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel S K R4 A G H N F C I O Q) :
    Prop :=
  Function.Surjective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I) ∧
    (∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      ∃ x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I,
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = q) ∧
      S.measurePackage.reflectionPositive ∧
        G.orbitModel.euclideanInvariantConstruction ∧
          G.orbitModel.gaugeInvariantConstruction

/-- The quotient projection model proves its bundled outputs. -/
theorem projectionOutputs_holds
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
    {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel S K R4 A G H N F C I O Q) :
    M.projectionOutputs :=
  ⟨M.quotientMapSurjective,
    M.quotientRepresentative,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The quotient closure induces a quotient projection model. -/
theorem nonempty_ofQuotientClosure
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
    (O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I)
    (Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O) :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel S K R4 A G H N F C I O Q) :=
  ⟨ofQuotientClosure S K R4 A G H N F C I O Q⟩

end EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel

end

end MathlibAnalytic
end MGAP4D
