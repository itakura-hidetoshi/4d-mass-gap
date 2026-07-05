import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Closure for the carrier-level equivalence between quotient classes and the selected section range. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure
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
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V)
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W)
    (Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X)
    (Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y)
    (T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z) where
  sectionRangeEquivModel :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivModel S K R4 A G H N F C I O Q P R U J V W X Y Z T
  sectionRangeEquivOutputs : sectionRangeEquivModel.sectionRangeEquivOutputs
  quotientToRange : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I →
    EuclideanYangMillsR4HilbertReconstructionQuotient.selectedSectionRangeCarrier I X
  rangeToQuotient : EuclideanYangMillsR4HilbertReconstructionQuotient.selectedSectionRangeCarrier I X →
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I
  rightInverse : ∀ q, rangeToQuotient (quotientToRange q) = q
  leftInverse : ∀ x, quotientToRange (rangeToQuotient x) = x
  sectionRepresentativeProjection :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I
        (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q) = q
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure

/-- Build the section-range equivalence closure from the representative projection closure. -/
def ofSectionRepresentativeProjectionClosure
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
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V)
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W)
    (Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X)
    (Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y)
    (T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T :=
  let M := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivModel.ofSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T
  { sectionRangeEquivModel := M
    sectionRangeEquivOutputs := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivModel.sectionRangeEquivOutputs_holds M
    quotientToRange := M.quotientToRange
    rangeToQuotient := M.rangeToQuotient
    rightInverse := M.rightInverse
    leftInverse := M.leftInverse
    sectionRepresentativeProjection := M.sectionRepresentativeProjection
    reflectionPositive := M.reflectionPositive
    euclideanInvariant := M.euclideanInvariant
    gaugeInvariant := M.gaugeInvariant }

/-- Build the section-range equivalence closure directly from the construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S
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
      (EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure.ofSpine S) :=
  ofSectionRepresentativeProjectionClosure S
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
    (EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure.ofSpine S)

/-- Extract the bundled section-range equivalence outputs. -/
theorem sectionRangeEquivOutputsHeld
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
    {X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W}
    {Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X}
    {Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y}
    {T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z}
    (E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T) :
    E.sectionRangeEquivModel.sectionRangeEquivOutputs :=
  E.sectionRangeEquivOutputs

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure

end

end MathlibAnalytic
end MGAP4D
