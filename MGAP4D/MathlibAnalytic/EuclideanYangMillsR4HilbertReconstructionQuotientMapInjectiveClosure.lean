import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Closure for quotient-map faithfulness on the selected section range in the R4 Hilbert reconstruction route. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure
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
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V) where
  quotientMapInjectiveModel :
    EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel S K R4 A G H N F C I O Q P R U J V W
  quotientMapInjectiveOutputs : quotientMapInjectiveModel.quotientMapInjectiveOutputs
  quotientMapReflectsSectionRangeEq :
    ∀ {x y : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ V.sectionRange → y ∈ V.sectionRange →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x =
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I y → x = y
  sectionRange : Set (EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I)
  sectionRange_eq : sectionRange = V.sectionRange
  sectionInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure

/-- Build the quotient-map faithfulness closure from the section-range uniqueness closure. -/
def ofSectionRangeUniqueClosure
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
    EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W :=
  let M := EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel.ofSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V W
  { quotientMapInjectiveModel := M
    quotientMapInjectiveOutputs := EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel.quotientMapInjectiveOutputs_holds M
    quotientMapReflectsSectionRangeEq := M.quotientMapReflectsSectionRangeEq
    sectionRange := M.sectionRange
    sectionRange_eq := M.sectionRange_eq
    sectionInjective := M.sectionInjective
    reflectionPositive := M.reflectionPositive
    euclideanInvariant := M.euclideanInvariant
    gaugeInvariant := M.gaugeInvariant }

/-- Build the quotient-map faithfulness closure directly from the construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
      (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationStructureClosure.ofSpine S)
      (EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionCarrierClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure.ofSpine S) :=
  ofSectionRangeUniqueClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
    (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationStructureClosure.ofSpine S)
    (EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionCarrierClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure.ofSpine S)

/-- Extract the bundled quotient-map section-range faithfulness outputs. -/
theorem quotientMapInjectiveOutputsHeld
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
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W) :
    X.quotientMapInjectiveModel.quotientMapInjectiveOutputs :=
  X.quotientMapInjectiveOutputs

end EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure

end

end MathlibAnalytic
end MGAP4D
