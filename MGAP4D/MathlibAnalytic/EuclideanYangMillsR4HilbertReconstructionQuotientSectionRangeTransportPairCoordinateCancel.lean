import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotient

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
variable {K : EuclideanYangMillsCompleteConstructionClosure S}
variable {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
variable {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
variable {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
variable {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
variable {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
variable {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
variable {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}

/-- Coordinate form of the quotient-generated transport cancellation. -/
theorem quotientPairCoordinate_cancel
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
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
    {E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T}
    {D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E}
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)
    (q : quotientCarrier I) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q := by
  simpa [quotientPairRangeCoord, quotientPairQuotientCoord] using TR.forward_inverse_cancel q

/-- Coordinate form of the range-generated transport cancellation. -/
theorem rangePairCoordinate_cancel
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
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
    {E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T}
    {D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E}
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)
    (x : selectedSectionRangeCarrier I X) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x := by
  simpa [rangePairQuotientCoord, rangePairRangeCoord] using TR.inverse_forward_cancel x

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Closure for coordinate-level cancellation of transport pairs. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancelClosure
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
    (T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z)
    (E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T)
    (D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E)
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)
    (PCL : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR)
    (PPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL)
    (TPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC)
    (CO : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC) where
  quotientCoordinate_cancel : ∀ q,
    TR.inverseTransport (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairRangeCoord I TR q) =
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairQuotientCoord I TR q
  rangeCoordinate_cancel : ∀ x,
    TR.forwardTransport (EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairQuotientCoord I TR x) =
      EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairRangeCoord I TR x
  quotientPairQuotientCoord_eq : ∀ q,
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairQuotientCoord I TR q = q
  quotientPairRangeCoord_eq : ∀ q,
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairRangeCoord I TR q = TR.forwardTransport q
  rangePairQuotientCoord_eq : ∀ x,
    EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairQuotientCoord I TR x = TR.inverseTransport x
  rangePairRangeCoord_eq : ∀ x,
    EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairRangeCoord I TR x = x
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancelClosure

/-- Build the coordinate-cancellation closure from the coordinate closure. -/
def ofCoordinateClosure
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
    (T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z)
    (E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T)
    (D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E)
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)
    (PCL : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR)
    (PPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL)
    (TPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC)
    (CO : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancelClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC CO :=
  { quotientCoordinate_cancel := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairCoordinate_cancel I TR
    rangeCoordinate_cancel := EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairCoordinate_cancel I TR
    quotientPairQuotientCoord_eq := CO.quotientPairQuotientCoord_eq
    quotientPairRangeCoord_eq := CO.quotientPairRangeCoord_eq
    rangePairQuotientCoord_eq := CO.rangePairQuotientCoord_eq
    rangePairRangeCoord_eq := CO.rangePairRangeCoord_eq
    reflectionPositive := CO.reflectionPositive
    euclideanInvariant := CO.euclideanInvariant
    gaugeInvariant := CO.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancelClosure

end

end MathlibAnalytic
end MGAP4D
