import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateRoundTripConsequences
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

/-- Build the quotient-generated proposition from split direct components. -/
theorem quotientPairCoordinateRoundTripProp_of_split_components (q : quotientCarrier I)
    (hinv : TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q)
    (hfwd : TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) :
    quotientPairCoordinateRoundTripProp I TR q := by
  exact quotientPairCoordinateRoundTripProp_of_components I TR q ⟨hinv, hfwd⟩

/-- Build the range-generated proposition from split direct components. -/
theorem rangePairCoordinateRoundTripProp_of_split_components (x : selectedSectionRangeCarrier I X)
    (hfwd : TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x)
    (hinv : TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) :
    rangePairCoordinateRoundTripProp I TR x := by
  exact rangePairCoordinateRoundTripProp_of_components I TR x ⟨hfwd, hinv⟩

/-- Build the quotient-generated proposition from split symmetric components. -/
theorem quotientPairCoordinateRoundTripProp_of_split_symmetric_components (q : quotientCarrier I)
    (hinv : quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q))
    (hfwd : quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q)) :
    quotientPairCoordinateRoundTripProp I TR q := by
  exact quotientPairCoordinateRoundTripProp_of_symmetric_components I TR q ⟨hinv, hfwd⟩

/-- Build the range-generated proposition from split symmetric components. -/
theorem rangePairCoordinateRoundTripProp_of_split_symmetric_components (x : selectedSectionRangeCarrier I X)
    (hfwd : rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x))
    (hinv : rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x)) :
    rangePairCoordinateRoundTripProp I TR x := by
  exact rangePairCoordinateRoundTripProp_of_symmetric_components I TR x ⟨hfwd, hinv⟩

/-- Extract the first symmetric quotient-generated component from a named proposition. -/
theorem quotientPairCoordinateRoundTripProp_inverse_symm_of_prop (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) := by
  exact h.1.symm

/-- Extract the second symmetric quotient-generated component from a named proposition. -/
theorem quotientPairCoordinateRoundTripProp_forward_symm_of_prop (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  exact h.2.symm

/-- Extract the first symmetric range-generated component from a named proposition. -/
theorem rangePairCoordinateRoundTripProp_forward_symm_of_prop (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) := by
  exact h.1.symm

/-- Extract the second symmetric range-generated component from a named proposition. -/
theorem rangePairCoordinateRoundTripProp_inverse_symm_of_prop (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  exact h.2.symm

/-- Direct and symmetric quotient-generated component conjunctions are equivalent. -/
theorem quotientPairCoordinateRoundTripProp_components_iff_symmetric_components (q : quotientCarrier I) :
    (TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) ↔
      quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
        quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  constructor
  · intro h
    exact quotientPairCoordinateRoundTripProp_components_to_symmetric_components I TR q h
  · intro h
    exact quotientPairCoordinateRoundTripProp_symmetric_components_to_components I TR q h

/-- Direct and symmetric range-generated component conjunctions are equivalent. -/
theorem rangePairCoordinateRoundTripProp_components_iff_symmetric_components (x : selectedSectionRangeCarrier I X) :
    (TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) ↔
      rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
        rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  constructor
  · intro h
    exact rangePairCoordinateRoundTripProp_components_to_symmetric_components I TR x h
  · intro h
    exact rangePairCoordinateRoundTripProp_symmetric_components_to_components I TR x h

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
