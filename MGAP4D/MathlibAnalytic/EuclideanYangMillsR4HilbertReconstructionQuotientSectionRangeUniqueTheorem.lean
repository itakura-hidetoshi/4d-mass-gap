import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel

/-- Bundled outputs for the quotient-section range uniqueness stage. -/
def sectionRangeUniqueOutputs
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
    {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel S K R4 A G H N F C I O Q P R U J V) :
    Prop :=
  (∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I}
      {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q →
        x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I r → q = r) ∧
    (∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I}
      {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = r → q = r) ∧
      (∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I}
        {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
        (x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∧
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = q) →
          (x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I r ∧
            EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = r) → q = r) ∧
        Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I) ∧
          S.measurePackage.reflectionPositive ∧
            G.orbitModel.euclideanInvariantConstruction ∧
              G.orbitModel.gaugeInvariantConstruction

/-- The quotient-section range uniqueness model proves its bundled outputs. -/
theorem sectionRangeUniqueOutputs_holds
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
    {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel S K R4 A G H N F C I O Q P R U J V) :
    M.sectionRangeUniqueOutputs :=
  ⟨M.witnessUnique,
    M.projectionUnique,
    M.fullWitnessUnique,
    M.sectionInjective,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The quotient-section range closure induces a uniqueness model for its witnesses. -/
theorem nonempty_ofSectionRangeClosure
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
    (J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U)
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J) :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel S K R4 A G H N F C I O Q P R U J V) :=
  ⟨ofSectionRangeClosure S K R4 A G H N F C I O Q P R U J V⟩

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel

end

end MathlibAnalytic
end MGAP4D
