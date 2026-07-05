import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateRoundTripOrientationIff
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
variable (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
variable {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
variable {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
variable {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
variable {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
variable {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
variable {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
variable {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
variable {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
variable {X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W}
variable {Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X}
variable {Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y}
variable {T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z}
variable {E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T}
variable {D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E}
variable (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)

/-- Symmetric and direct quotient-generated inverse component orientations are equivalent. -/
theorem quotientPairCoordinateRoundTripProp_symmetric_inverse_iff_inverse (q : quotientCarrier I) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ↔
      TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q := by
  exact (quotientPairCoordinateRoundTripProp_inverse_iff_symmetric_inverse I TR q).symm

/-- Symmetric and direct quotient-generated forward component orientations are equivalent. -/
theorem quotientPairCoordinateRoundTripProp_symmetric_forward_iff_forward (q : quotientCarrier I) :
    quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) ↔
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact (quotientPairCoordinateRoundTripProp_forward_iff_symmetric_forward I TR q).symm

/-- Symmetric and direct range-generated forward component orientations are equivalent. -/
theorem rangePairCoordinateRoundTripProp_symmetric_forward_iff_forward (x : selectedSectionRangeCarrier I X) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ↔
      TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x := by
  exact (rangePairCoordinateRoundTripProp_forward_iff_symmetric_forward I TR x).symm

/-- Symmetric and direct range-generated inverse component orientations are equivalent. -/
theorem rangePairCoordinateRoundTripProp_symmetric_inverse_iff_inverse (x : selectedSectionRangeCarrier I X) :
    rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) ↔
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact (rangePairCoordinateRoundTripProp_inverse_iff_symmetric_inverse I TR x).symm

/-- Direct quotient-generated components are equivalent to the named proposition. -/
theorem quotientPairCoordinateRoundTripProp_components_iff_prop (q : quotientCarrier I) :
    (TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) ↔
      quotientPairCoordinateRoundTripProp I TR q := by
  exact (quotientPairCoordinateRoundTripProp_iff_components I TR q).symm

/-- Direct range-generated components are equivalent to the named proposition. -/
theorem rangePairCoordinateRoundTripProp_components_iff_prop (x : selectedSectionRangeCarrier I X) :
    (TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) ↔
      rangePairCoordinateRoundTripProp I TR x := by
  exact (rangePairCoordinateRoundTripProp_iff_components I TR x).symm

/-- Symmetric quotient-generated components are equivalent to the named proposition. -/
theorem quotientPairCoordinateRoundTripProp_symmetric_components_iff_prop (q : quotientCarrier I) :
    (quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q)) ↔
      quotientPairCoordinateRoundTripProp I TR q := by
  exact (quotientPairCoordinateRoundTripProp_iff_symmetric_components I TR q).symm

/-- Symmetric range-generated components are equivalent to the named proposition. -/
theorem rangePairCoordinateRoundTripProp_symmetric_components_iff_prop (x : selectedSectionRangeCarrier I X) :
    (rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x)) ↔
      rangePairCoordinateRoundTripProp I TR x := by
  exact (rangePairCoordinateRoundTripProp_iff_symmetric_components I TR x).symm

/-- Symmetric and direct quotient-generated component conjunctions are equivalent. -/
theorem quotientPairCoordinateRoundTripProp_symmetric_components_iff_components (q : quotientCarrier I) :
    (quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q)) ↔
      TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
        TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact (quotientPairCoordinateRoundTripProp_components_iff_symmetric_components I TR q).symm

/-- Symmetric and direct range-generated component conjunctions are equivalent. -/
theorem rangePairCoordinateRoundTripProp_symmetric_components_iff_components (x : selectedSectionRangeCarrier I X) :
    (rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x)) ↔
      TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
        TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact (rangePairCoordinateRoundTripProp_components_iff_symmetric_components I TR x).symm

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
