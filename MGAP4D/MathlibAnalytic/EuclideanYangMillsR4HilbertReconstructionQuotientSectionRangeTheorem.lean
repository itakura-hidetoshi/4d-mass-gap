import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel

/-- Bundled outputs for the quotient-section range stage. -/
def sectionRangeOutputs
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
    {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
    {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
    {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
    {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel S K R4 A G H N F C I O Q P R U J) :
    Prop :=
  (∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∈ M.sectionRange) ∧
    (∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ M.sectionRange →
        ∃ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q = x) ∧
      (∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
        x ∈ M.sectionRange →
          ∃ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
            x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∧
              EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = q) ∧
        Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I) ∧
          S.measurePackage.reflectionPositive ∧
            G.orbitModel.euclideanInvariantConstruction ∧
              G.orbitModel.gaugeInvariantConstruction

/-- The quotient-section range model proves its bundled outputs. -/
theorem sectionRangeOutputs_holds
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
    {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
    {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
    {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
    {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel S K R4 A G H N F C I O Q P R U J) :
    M.sectionRangeOutputs :=
  ⟨M.sectionMemRange,
    M.rangeHasClass,
    M.rangeProjectsToWitness,
    M.sectionInjective,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The quotient-section injectivity closure induces a quotient-section range model. -/
theorem nonempty_ofSectionInjectiveClosure
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
    (Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O)
    (P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q)
    (R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P)
    (U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R)
    (J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U) :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel S K R4 A G H N F C I O Q P R U J) :=
  ⟨ofSectionInjectiveClosure S K R4 A G H N F C I O Q P R U J⟩

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel

end

end MathlibAnalytic
end MGAP4D
