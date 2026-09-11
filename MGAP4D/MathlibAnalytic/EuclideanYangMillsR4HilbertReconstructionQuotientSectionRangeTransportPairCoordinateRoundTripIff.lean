import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairCoordinateRoundTripPropSymmRecompose
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

/-- The named quotient-generated round-trip proposition is exactly its component conjunction. -/
theorem quotientPairCoordinateRoundTripProp_iff_components (q : quotientCarrier I) :
    quotientPairCoordinateRoundTripProp I TR q ↔
      TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
        TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q := by
  rfl

/-- The named range-generated round-trip proposition is exactly its component conjunction. -/
theorem rangePairCoordinateRoundTripProp_iff_components (x : selectedSectionRangeCarrier I X) :
    rangePairCoordinateRoundTripProp I TR x ↔
      TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
        TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x := by
  rfl

/-- The named quotient-generated round-trip proposition is equivalent to symmetric component orientations. -/
theorem quotientPairCoordinateRoundTripProp_iff_symmetric_components (q : quotientCarrier I) :
    quotientPairCoordinateRoundTripProp I TR q ↔
      quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
        quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) := by
  constructor
  · intro h
    exact ⟨h.1.symm, h.2.symm⟩
  · intro h
    exact ⟨h.1.symm, h.2.symm⟩

/-- The named range-generated round-trip proposition is equivalent to symmetric component orientations. -/
theorem rangePairCoordinateRoundTripProp_iff_symmetric_components (x : selectedSectionRangeCarrier I X) :
    rangePairCoordinateRoundTripProp I TR x ↔
      rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
        rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) := by
  constructor
  · intro h
    exact ⟨h.1.symm, h.2.symm⟩
  · intro h
    exact ⟨h.1.symm, h.2.symm⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
