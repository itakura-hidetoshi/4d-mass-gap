import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel

/-- Bundled outputs for the quotient-section injectivity stage. -/
def sectionInjectiveOutputs
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
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel S K R4 A G H N F C I O Q P R U) :
    Prop :=
  Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I) ∧
    (∀ {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q =
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I r → q = r) ∧
      (∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I
          (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q) = q) ∧
        S.measurePackage.reflectionPositive ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            G.orbitModel.gaugeInvariantConstruction

/-- The quotient-section injectivity model proves its bundled outputs. -/
theorem sectionInjectiveOutputs_holds
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
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel S K R4 A G H N F C I O Q P R U) :
    M.sectionInjectiveOutputs :=
  ⟨M.sectionInjective,
    M.sectionEqReflectsClass,
    M.sectionProjects,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The quotient-section closure induces a quotient-section injectivity model. -/
theorem nonempty_ofSectionClosure
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
    (U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R) :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel S K R4 A G H N F C I O Q P R U) :=
  ⟨ofSectionClosure S K R4 A G H N F C I O Q P R U⟩

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel

end

end MathlibAnalytic
end MGAP4D
