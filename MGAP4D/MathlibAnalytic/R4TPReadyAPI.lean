import MGAP4D.MathlibAnalytic.R4TransportPairCompletionDataAPI
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

theorem quotientPairCoordinateRoundTripProp_direct_components_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact quotientPairCoordinateRoundTripProp_direct_components_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_direct_components_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact rangePairCoordinateRoundTripProp_direct_components_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_symmetric_components_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  exact quotientPairCoordinateRoundTripProp_symmetric_components_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_symmetric_components_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  exact rangePairCoordinateRoundTripProp_symmetric_components_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_direct_components_from_symmetric_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact quotientPairCoordinateRoundTripProp_direct_components_from_symmetric_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_direct_components_from_symmetric_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact rangePairCoordinateRoundTripProp_direct_components_from_symmetric_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_symmetric_components_from_direct_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  exact quotientPairCoordinateRoundTripProp_symmetric_components_from_direct_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_symmetric_components_from_direct_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  exact rangePairCoordinateRoundTripProp_symmetric_components_from_direct_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_inverse_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q := by
  exact quotientPairCoordinateRoundTripProp_inverse_completion_data I TR q h

theorem quotientPairCoordinateRoundTripProp_forward_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact quotientPairCoordinateRoundTripProp_forward_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_forward_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x := by
  exact rangePairCoordinateRoundTripProp_forward_completion_data I TR x h

theorem rangePairCoordinateRoundTripProp_inverse_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact rangePairCoordinateRoundTripProp_inverse_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_symmetric_inverse_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) := by
  exact quotientPairCoordinateRoundTripProp_symmetric_inverse_completion_data I TR q h

theorem quotientPairCoordinateRoundTripProp_symmetric_forward_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  exact quotientPairCoordinateRoundTripProp_symmetric_forward_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_symmetric_forward_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) := by
  exact rangePairCoordinateRoundTripProp_symmetric_forward_completion_data I TR x h

theorem rangePairCoordinateRoundTripProp_symmetric_inverse_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  exact rangePairCoordinateRoundTripProp_symmetric_inverse_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_inverse_symm_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) := by
  exact quotientPairCoordinateRoundTripProp_inverse_symm_completion_data I TR q h

theorem quotientPairCoordinateRoundTripProp_forward_symm_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  exact quotientPairCoordinateRoundTripProp_forward_symm_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_forward_symm_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) := by
  exact rangePairCoordinateRoundTripProp_forward_symm_completion_data I TR x h

theorem rangePairCoordinateRoundTripProp_inverse_symm_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  exact rangePairCoordinateRoundTripProp_inverse_symm_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_inverse_direct_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q := by
  exact quotientPairCoordinateRoundTripProp_inverse_direct_completion_data I TR q h

theorem quotientPairCoordinateRoundTripProp_forward_direct_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  exact quotientPairCoordinateRoundTripProp_forward_direct_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_forward_direct_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x := by
  exact rangePairCoordinateRoundTripProp_forward_direct_completion_data I TR x h

theorem rangePairCoordinateRoundTripProp_inverse_direct_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  exact rangePairCoordinateRoundTripProp_inverse_direct_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_recompose_direct_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairCoordinateRoundTripProp I TR q := by
  exact quotientPairCoordinateRoundTripProp_recompose_direct_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_recompose_direct_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairCoordinateRoundTripProp I TR x := by
  exact rangePairCoordinateRoundTripProp_recompose_direct_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_recompose_symmetric_ready (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairCoordinateRoundTripProp I TR q := by
  exact quotientPairCoordinateRoundTripProp_recompose_symmetric_completion_data I TR q h

theorem rangePairCoordinateRoundTripProp_recompose_symmetric_ready (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairCoordinateRoundTripProp I TR x := by
  exact rangePairCoordinateRoundTripProp_recompose_symmetric_completion_data I TR x h

theorem quotientPairCoordinateRoundTripProp_of_direct_components_ready (q : quotientCarrier I)
    (hinv : TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q)
    (hfwd : TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) :
    quotientPairCoordinateRoundTripProp I TR q := by
  exact quotientPairCoordinateRoundTripProp_of_direct_components_completion_data I TR q hinv hfwd

theorem rangePairCoordinateRoundTripProp_of_direct_components_ready (x : selectedSectionRangeCarrier I X)
    (hfwd : TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x)
    (hinv : TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) :
    rangePairCoordinateRoundTripProp I TR x := by
  exact rangePairCoordinateRoundTripProp_of_direct_components_completion_data I TR x hfwd hinv

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
