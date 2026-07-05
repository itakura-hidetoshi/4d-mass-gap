import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateRoundTripReverseIff
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

/-- Project the quotient-generated inverse component from a direct component conjunction. -/
theorem quotientPairCoordinateRoundTripProp_inverse_of_components (q : quotientCarrier I)
    (h : TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q := by
  exact h.1

/-- Project the quotient-generated forward component from a direct component conjunction. -/
theorem quotientPairCoordinateRoundTripProp_forward_of_components (q : quotientCarrier I)
    (h : TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) :
    TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact h.2

/-- Project the range-generated forward component from a direct component conjunction. -/
theorem rangePairCoordinateRoundTripProp_forward_of_components (x : selectedSectionRangeCarrier I X)
    (h : TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x := by
  exact h.1

/-- Project the range-generated inverse component from a direct component conjunction. -/
theorem rangePairCoordinateRoundTripProp_inverse_of_components (x : selectedSectionRangeCarrier I X)
    (h : TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) :
    TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact h.2

/-- Project the symmetric quotient-generated inverse component from a symmetric component conjunction. -/
theorem quotientPairCoordinateRoundTripProp_symmetric_inverse_of_symmetric_components (q : quotientCarrier I)
    (h : quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q)) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) := by
  exact h.1

/-- Project the symmetric quotient-generated forward component from a symmetric component conjunction. -/
theorem quotientPairCoordinateRoundTripProp_symmetric_forward_of_symmetric_components (q : quotientCarrier I)
    (h : quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q)) :
    quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  exact h.2

/-- Project the symmetric range-generated forward component from a symmetric component conjunction. -/
theorem rangePairCoordinateRoundTripProp_symmetric_forward_of_symmetric_components (x : selectedSectionRangeCarrier I X)
    (h : rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x)) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) := by
  exact h.1

/-- Project the symmetric range-generated inverse component from a symmetric component conjunction. -/
theorem rangePairCoordinateRoundTripProp_symmetric_inverse_of_symmetric_components (x : selectedSectionRangeCarrier I X)
    (h : rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x)) :
    rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  exact h.2

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
