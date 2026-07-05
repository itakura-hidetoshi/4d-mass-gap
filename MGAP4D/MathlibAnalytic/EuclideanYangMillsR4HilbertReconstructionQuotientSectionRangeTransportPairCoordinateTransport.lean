import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancel
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

/-- Coordinate form of forward transport on a quotient-generated pair. -/
theorem quotientPairCoordinate_forward
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
    TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q :=
  rfl

/-- Coordinate form of inverse transport on a range-generated pair. -/
theorem rangePairCoordinate_inverse
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
    TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x :=
  rfl

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Closure for coordinate-level transport identities. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateTransportClosure
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
    (CO : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC)
    (CC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancelClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC CO) where
  quotientCoordinate_forward : ∀ q,
    TR.forwardTransport (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairQuotientCoord I TR q) =
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairRangeCoord I TR q
  rangeCoordinate_inverse : ∀ x,
    TR.inverseTransport (EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairRangeCoord I TR x) =
      EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairQuotientCoord I TR x
  quotientCoordinate_cancel : ∀ q,
    TR.inverseTransport (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairRangeCoord I TR q) =
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairQuotientCoord I TR q
  rangeCoordinate_cancel : ∀ x,
    TR.forwardTransport (EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairQuotientCoord I TR x) =
      EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairRangeCoord I TR x
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateTransportClosure

/-- Build the coordinate-transport closure from coordinate cancellation. -/
def ofCoordinateCancelClosure
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
    (CO : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC)
    (CC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateCancelClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC CO) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC TPC CO CC :=
  { quotientCoordinate_forward := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientPairCoordinate_forward I TR
    rangeCoordinate_inverse := EuclideanYangMillsR4HilbertReconstructionQuotient.rangePairCoordinate_inverse I TR
    quotientCoordinate_cancel := CC.quotientCoordinate_cancel
    rangeCoordinate_cancel := CC.rangeCoordinate_cancel
    reflectionPositive := CC.reflectionPositive
    euclideanInvariant := CC.euclideanInvariant
    gaugeInvariant := CC.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateTransportClosure

end

end MathlibAnalytic
end MGAP4D
