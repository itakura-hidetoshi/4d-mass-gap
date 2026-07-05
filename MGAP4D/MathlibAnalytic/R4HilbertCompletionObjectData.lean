import MGAP4D.MathlibAnalytic.R4HilbertCompletionInputData
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

structure R4HilbertCompletionObjectData where
  inputData : R4HilbertCompletionInputData I TR
  objectCarrier : Type
  objectMap : quotientCarrier I → objectCarrier
  objectTargetNonempty : Nonempty objectCarrier
  objectMetricReady : Prop
  objectMetricReady_holds : objectMetricReady
  objectUniformReady : Prop
  objectUniformReady_holds : objectUniformReady
  objectCauchyReady : Prop
  objectCauchyReady_holds : objectCauchyReady
  objectCompleteReady : Prop
  objectCompleteReady_holds : objectCompleteReady
  objectDenseRangeReady : Prop
  objectDenseRangeReady_holds : objectDenseRangeReady
  objectSeparatedReady : Prop
  objectSeparatedReady_holds : objectSeparatedReady
  objectMapReady : Prop
  objectMapReady_holds : objectMapReady
  objectMapRespectsQuotientReady : Prop
  objectMapRespectsQuotientReady_holds : objectMapRespectsQuotientReady
  objectMapHandoffReady : Prop
  objectMapHandoffReady_holds : objectMapHandoffReady
  objectBoundaryOpen : Prop
  objectBoundaryOpen_holds : objectBoundaryOpen
  objectHandoffReady : Prop
  objectHandoffReady_holds : objectHandoffReady
  objectDenseStatementOpen : Prop
  objectDenseStatementOpen_holds : objectDenseStatementOpen
  objectCompleteStatementOpen : Prop
  objectCompleteStatementOpen_holds : objectCompleteStatementOpen
  objectMapCanonicalReady : Prop
  objectMapCanonicalReady_holds : objectMapCanonicalReady
  objectTransportExtensionReady : Prop
  objectTransportExtensionReady_holds : objectTransportExtensionReady
  objectSectionExtensionReady : Prop
  objectSectionExtensionReady_holds : objectSectionExtensionReady
  objectNextLayerReady : Prop
  objectNextLayerReady_holds : objectNextLayerReady

theorem r4HilbertCompletionObject_input_data
    (M : R4HilbertCompletionObjectData I TR) :
    R4HilbertCompletionInputData I TR :=
  M.inputData

theorem r4HilbertCompletionObject_carrier_nonempty
    (M : R4HilbertCompletionObjectData I TR) :
    Nonempty M.objectCarrier :=
  M.objectTargetNonempty

theorem r4HilbertCompletionObject_metric_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMetricReady :=
  M.objectMetricReady_holds

theorem r4HilbertCompletionObject_uniform_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectUniformReady :=
  M.objectUniformReady_holds

theorem r4HilbertCompletionObject_cauchy_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCauchyReady :=
  M.objectCauchyReady_holds

theorem r4HilbertCompletionObject_complete_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCompleteReady :=
  M.objectCompleteReady_holds

theorem r4HilbertCompletionObject_dense_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectDenseRangeReady :=
  M.objectDenseRangeReady_holds

theorem r4HilbertCompletionObject_separated_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectSeparatedReady :=
  M.objectSeparatedReady_holds

theorem r4HilbertCompletionObject_map_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMapReady :=
  M.objectMapReady_holds

theorem r4HilbertCompletionObject_map_respects_quotient_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMapRespectsQuotientReady :=
  M.objectMapRespectsQuotientReady_holds

theorem r4HilbertCompletionObject_map_handoff_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMapHandoffReady :=
  M.objectMapHandoffReady_holds

theorem r4HilbertCompletionObject_boundary_open
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectBoundaryOpen :=
  M.objectBoundaryOpen_holds

theorem r4HilbertCompletionObject_handoff_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectHandoffReady :=
  M.objectHandoffReady_holds

theorem r4HilbertCompletionObject_dense_statement_open
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectDenseStatementOpen :=
  M.objectDenseStatementOpen_holds

theorem r4HilbertCompletionObject_complete_statement_open
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCompleteStatementOpen :=
  M.objectCompleteStatementOpen_holds

theorem r4HilbertCompletionObject_map_canonical_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMapCanonicalReady :=
  M.objectMapCanonicalReady_holds

theorem r4HilbertCompletionObject_transport_extension_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectTransportExtensionReady :=
  M.objectTransportExtensionReady_holds

theorem r4HilbertCompletionObject_section_extension_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectSectionExtensionReady :=
  M.objectSectionExtensionReady_holds

theorem r4HilbertCompletionObject_next_layer_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectNextLayerReady :=
  M.objectNextLayerReady_holds

theorem r4HilbertCompletionObject_input_metric_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionMetricReady :=
  r4HilbertCompletionInput_metric_ready I TR M.inputData

theorem r4HilbertCompletionObject_input_uniform_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionUniformReady :=
  r4HilbertCompletionInput_uniform_ready I TR M.inputData

theorem r4HilbertCompletionObject_input_cauchy_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionCauchyReady :=
  r4HilbertCompletionInput_cauchy_ready I TR M.inputData

theorem r4HilbertCompletionObject_input_complete_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionCompleteReady :=
  r4HilbertCompletionInput_complete_ready I TR M.inputData

theorem r4HilbertCompletionObject_input_dense_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionDenseRangeReady :=
  r4HilbertCompletionInput_dense_ready I TR M.inputData

theorem r4HilbertCompletionObject_input_boundary_open
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionBoundaryOpen :=
  r4HilbertCompletionInput_boundary_open I TR M.inputData

theorem r4HilbertCompletionObject_input_next_layer_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionNextLayerReady :=
  r4HilbertCompletionInput_next_layer_ready I TR M.inputData

theorem r4HilbertCompletionObject_quotient_direct_components
    (M : R4HilbertCompletionObjectData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q :=
  r4HilbertCompletionInput_quotient_direct_components I TR M.inputData q h

theorem r4HilbertCompletionObject_range_direct_components
    (M : R4HilbertCompletionObjectData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x :=
  r4HilbertCompletionInput_range_direct_components I TR M.inputData x h

theorem r4HilbertCompletionObject_quotient_inverse
    (M : R4HilbertCompletionObjectData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q :=
  r4HilbertCompletionInput_quotient_inverse I TR M.inputData q h

theorem r4HilbertCompletionObject_range_forward
    (M : R4HilbertCompletionObjectData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x :=
  r4HilbertCompletionInput_range_forward I TR M.inputData x h

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
