import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel

/-- Bundled outputs for the quotient-map injectivity stage. -/
def quotientMapInjectiveOutputs
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
    {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel S K R4 A G H N F C I O Q P R U J V W) :
    Prop :=
  (∀ {x y : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x =
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I y → x = y) ∧
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I) ∧
      Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I) ∧
        S.measurePackage.reflectionPositive ∧
          G.orbitModel.euclideanInvariantConstruction ∧
            G.orbitModel.gaugeInvariantConstruction

/-- The quotient-map injectivity model proves its bundled outputs. -/
theorem quotientMapInjectiveOutputs_holds
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
    {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
    (M : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel S K R4 A G H N F C I O Q P R U J V W) :
    M.quotientMapInjectiveOutputs :=
  ⟨M.quotientMapReflectsInputEq,
    M.quotientMapInjective,
    M.sectionInjective,
    M.reflectionPositive,
    M.euclideanInvariant,
    M.gaugeInvariant⟩

/-- The section-range uniqueness closure induces a quotient-map injectivity model. -/
theorem nonempty_ofSectionRangeUniqueClosure
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
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J)
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V) :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel S K R4 A G H N F C I O Q P R U J V W) :=
  ⟨ofSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V W⟩

end EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel

end

end MathlibAnalytic
end MGAP4D
