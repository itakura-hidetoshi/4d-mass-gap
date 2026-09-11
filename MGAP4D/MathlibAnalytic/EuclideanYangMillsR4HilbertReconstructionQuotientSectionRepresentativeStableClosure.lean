import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Closure for stability of selected quotient-section representatives. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure
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
    (Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X) where
  sectionRepresentativeStableModel :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableModel S K R4 A G H N F C I O Q P R U J V W X Y
  sectionRepresentativeStableOutputs : sectionRepresentativeStableModel.sectionRepresentativeStableOutputs
  sectionRepresentativeMemRange :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∈ X.sectionRange
  sectionRepresentativeRoundTrip :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I
        (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I
          (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q)) =
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q
  sectionRangeRoundTrip :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ X.sectionRange →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I
          (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x) = x
  sectionRange_eq : X.sectionRange = V.sectionRange
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure

/-- Build the selected representative stability closure from the section-range round-trip closure. -/
def ofSectionRangeRoundTripClosure
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
    (Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y :=
  let M := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableModel.ofSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X Y
  { sectionRepresentativeStableModel := M
    sectionRepresentativeStableOutputs := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableModel.sectionRepresentativeStableOutputs_holds M
    sectionRepresentativeMemRange := M.sectionRepresentativeMemRange
    sectionRepresentativeRoundTrip := M.sectionRepresentativeRoundTrip
    sectionRangeRoundTrip := M.sectionRangeRoundTrip
    sectionRange_eq := M.sectionRange_eq
    reflectionPositive := M.reflectionPositive
    euclideanInvariant := M.euclideanInvariant
    gaugeInvariant := M.gaugeInvariant }

/-- Build the selected representative stability closure directly from the construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S
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
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure.ofSpine S) :=
  ofSectionRangeRoundTripClosure S
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

/-- Extract the bundled selected representative stability outputs. -/
theorem sectionRepresentativeStableOutputsHeld
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
    (Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y) :
    Z.sectionRepresentativeStableModel.sectionRepresentativeStableOutputs :=
  Z.sectionRepresentativeStableOutputs

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure

end

end MathlibAnalytic
end MGAP4D
