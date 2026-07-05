import MGAP4D.MathlibAnalytic.R4TPHandoffAPI
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

structure R4HilbertCompletionInputData where
  completedCarrier : Type
  completionMap : quotientCarrier I → completedCarrier
  completionTargetNonempty : Nonempty completedCarrier
  completionMetricReady : Prop
  completionMetricReady_holds : completionMetricReady
  completionUniformReady : Prop
  completionUniformReady_holds : completionUniformReady
  completionCauchyReady : Prop
  completionCauchyReady_holds : completionCauchyReady
  completionCompleteReady : Prop
  completionCompleteReady_holds : completionCompleteReady
  completionDenseRangeReady : Prop
  completionDenseRangeReady_holds : completionDenseRangeReady
  completionSeparatedReady : Prop
  completionSeparatedReady_holds : completionSeparatedReady
  completionMapReady : Prop
  completionMapReady_holds : completionMapReady
  completionMapRespectsQuotientReady : Prop
  completionMapRespectsQuotientReady_holds : completionMapRespectsQuotientReady
  completionMapHandoffReady : Prop
  completionMapHandoffReady_holds : completionMapHandoffReady
  quotientDirectComponentsReady : ∀ q,
    quotientPairCoordinateRoundTripProp I TR q →
      TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
        TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q
  rangeDirectComponentsReady : ∀ x,
    rangePairCoordinateRoundTripProp I TR x →
      TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
        TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x
  quotientSymmetricComponentsReady : ∀ q,
    quotientPairCoordinateRoundTripProp I TR q →
      quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
        quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q)
  rangeSymmetricComponentsReady : ∀ x,
    rangePairCoordinateRoundTripProp I TR x →
      rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
        rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x)
  quotientInverseReady : ∀ q,
    quotientPairCoordinateRoundTripProp I TR q →
      TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q
  quotientForwardReady : ∀ q,
    quotientPairCoordinateRoundTripProp I TR q →
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q
  rangeForwardReady : ∀ x,
    rangePairCoordinateRoundTripProp I TR x →
      TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x
  rangeInverseReady : ∀ x,
    rangePairCoordinateRoundTripProp I TR x →
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x
  quotientRecomposeReady : ∀ q,
    quotientPairCoordinateRoundTripProp I TR q → quotientPairCoordinateRoundTripProp I TR q
  rangeRecomposeReady : ∀ x,
    rangePairCoordinateRoundTripProp I TR x → rangePairCoordinateRoundTripProp I TR x
  quotientOfDirectComponentsReady : ∀ q,
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q →
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q →
        quotientPairCoordinateRoundTripProp I TR q
  rangeOfDirectComponentsReady : ∀ x,
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x →
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x →
        rangePairCoordinateRoundTripProp I TR x
  completionBoundaryOpen : Prop
  completionBoundaryOpen_holds : completionBoundaryOpen
  completionHandoffReady : Prop
  completionHandoffReady_holds : completionHandoffReady
  completionDenseStatementOpen : Prop
  completionDenseStatementOpen_holds : completionDenseStatementOpen
  completionCompleteStatementOpen : Prop
  completionCompleteStatementOpen_holds : completionCompleteStatementOpen
  completionMapCanonicalReady : Prop
  completionMapCanonicalReady_holds : completionMapCanonicalReady
  completionTransportExtensionReady : Prop
  completionTransportExtensionReady_holds : completionTransportExtensionReady
  completionSectionExtensionReady : Prop
  completionSectionExtensionReady_holds : completionSectionExtensionReady
  completionNextLayerReady : Prop
  completionNextLayerReady_holds : completionNextLayerReady

theorem r4HilbertCompletionInput_completedCarrier_nonempty
    (M : R4HilbertCompletionInputData I TR) :
    Nonempty M.completedCarrier :=
  M.completionTargetNonempty

theorem r4HilbertCompletionInput_metric_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionMetricReady :=
  M.completionMetricReady_holds

theorem r4HilbertCompletionInput_uniform_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionUniformReady :=
  M.completionUniformReady_holds

theorem r4HilbertCompletionInput_cauchy_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionCauchyReady :=
  M.completionCauchyReady_holds

theorem r4HilbertCompletionInput_complete_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionCompleteReady :=
  M.completionCompleteReady_holds

theorem r4HilbertCompletionInput_dense_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionDenseRangeReady :=
  M.completionDenseRangeReady_holds

theorem r4HilbertCompletionInput_separated_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionSeparatedReady :=
  M.completionSeparatedReady_holds

theorem r4HilbertCompletionInput_map_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionMapReady :=
  M.completionMapReady_holds

theorem r4HilbertCompletionInput_map_respects_quotient_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionMapRespectsQuotientReady :=
  M.completionMapRespectsQuotientReady_holds

theorem r4HilbertCompletionInput_map_handoff_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionMapHandoffReady :=
  M.completionMapHandoffReady_holds

theorem r4HilbertCompletionInput_quotient_direct_components
    (M : R4HilbertCompletionInputData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q :=
  M.quotientDirectComponentsReady q h

theorem r4HilbertCompletionInput_range_direct_components
    (M : R4HilbertCompletionInputData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x :=
  M.rangeDirectComponentsReady x h

theorem r4HilbertCompletionInput_quotient_symmetric_components
    (M : R4HilbertCompletionInputData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairQuotientCoord I TR q = TR.inverseTransport (quotientPairRangeCoord I TR q) ∧
      quotientPairRangeCoord I TR q = TR.forwardTransport (quotientPairQuotientCoord I TR q) :=
  M.quotientSymmetricComponentsReady q h

theorem r4HilbertCompletionInput_range_symmetric_components
    (M : R4HilbertCompletionInputData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairRangeCoord I TR x = TR.forwardTransport (rangePairQuotientCoord I TR x) ∧
      rangePairQuotientCoord I TR x = TR.inverseTransport (rangePairRangeCoord I TR x) :=
  M.rangeSymmetricComponentsReady x h

theorem r4HilbertCompletionInput_quotient_inverse
    (M : R4HilbertCompletionInputData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q :=
  M.quotientInverseReady q h

theorem r4HilbertCompletionInput_quotient_forward
    (M : R4HilbertCompletionInputData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q :=
  M.quotientForwardReady q h

theorem r4HilbertCompletionInput_range_forward
    (M : R4HilbertCompletionInputData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x :=
  M.rangeForwardReady x h

theorem r4HilbertCompletionInput_range_inverse
    (M : R4HilbertCompletionInputData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x :=
  M.rangeInverseReady x h

theorem r4HilbertCompletionInput_quotient_recompose
    (M : R4HilbertCompletionInputData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    quotientPairCoordinateRoundTripProp I TR q :=
  M.quotientRecomposeReady q h

theorem r4HilbertCompletionInput_range_recompose
    (M : R4HilbertCompletionInputData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    rangePairCoordinateRoundTripProp I TR x :=
  M.rangeRecomposeReady x h

theorem r4HilbertCompletionInput_quotient_of_direct_components
    (M : R4HilbertCompletionInputData I TR) (q : quotientCarrier I)
    (hinv : TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q)
    (hfwd : TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) :
    quotientPairCoordinateRoundTripProp I TR q :=
  M.quotientOfDirectComponentsReady q hinv hfwd

theorem r4HilbertCompletionInput_range_of_direct_components
    (M : R4HilbertCompletionInputData I TR) (x : selectedSectionRangeCarrier I X)
    (hfwd : TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x)
    (hinv : TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) :
    rangePairCoordinateRoundTripProp I TR x :=
  M.rangeOfDirectComponentsReady x hfwd hinv

theorem r4HilbertCompletionInput_boundary_open
    (M : R4HilbertCompletionInputData I TR) :
    M.completionBoundaryOpen :=
  M.completionBoundaryOpen_holds

theorem r4HilbertCompletionInput_handoff_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionHandoffReady :=
  M.completionHandoffReady_holds

theorem r4HilbertCompletionInput_dense_statement_open
    (M : R4HilbertCompletionInputData I TR) :
    M.completionDenseStatementOpen :=
  M.completionDenseStatementOpen_holds

theorem r4HilbertCompletionInput_complete_statement_open
    (M : R4HilbertCompletionInputData I TR) :
    M.completionCompleteStatementOpen :=
  M.completionCompleteStatementOpen_holds

theorem r4HilbertCompletionInput_map_canonical_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionMapCanonicalReady :=
  M.completionMapCanonicalReady_holds

theorem r4HilbertCompletionInput_transport_extension_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionTransportExtensionReady :=
  M.completionTransportExtensionReady_holds

theorem r4HilbertCompletionInput_section_extension_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionSectionExtensionReady :=
  M.completionSectionExtensionReady_holds

theorem r4HilbertCompletionInput_next_layer_ready
    (M : R4HilbertCompletionInputData I TR) :
    M.completionNextLayerReady :=
  M.completionNextLayerReady_holds

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
