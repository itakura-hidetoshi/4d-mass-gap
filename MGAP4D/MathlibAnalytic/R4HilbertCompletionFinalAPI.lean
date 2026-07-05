import MGAP4D.MathlibAnalytic.R4HilbertCompletionTransportAPI
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

theorem r4HilbertCompletionFinal_metric_uniform
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMetricReady ∧ M.objectUniformReady :=
  ⟨r4HilbertCompletionReadiness_metric I TR M,
    r4HilbertCompletionReadiness_uniform I TR M⟩

theorem r4HilbertCompletionFinal_cauchy_complete
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCauchyReady ∧ M.objectCompleteReady :=
  ⟨r4HilbertCompletionReadiness_cauchy I TR M,
    r4HilbertCompletionReadiness_complete I TR M⟩

theorem r4HilbertCompletionFinal_dense_separated
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectDenseRangeReady ∧ M.objectSeparatedReady :=
  ⟨r4HilbertCompletionReadiness_dense I TR M,
    r4HilbertCompletionReadiness_separated I TR M⟩

theorem r4HilbertCompletionFinal_boundary_handoff
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectBoundaryOpen ∧ M.objectHandoffReady :=
  ⟨r4HilbertCompletionReadiness_boundary I TR M,
    r4HilbertCompletionReadiness_handoff I TR M⟩

theorem r4HilbertCompletionFinal_statement_open
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectDenseStatementOpen ∧ M.objectCompleteStatementOpen :=
  ⟨r4HilbertCompletionReadiness_dense_statement I TR M,
    r4HilbertCompletionReadiness_complete_statement I TR M⟩

theorem r4HilbertCompletionFinal_extension_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectTransportExtensionReady ∧ M.objectSectionExtensionReady :=
  ⟨r4HilbertCompletionReadiness_transport_extension I TR M,
    r4HilbertCompletionReadiness_section_extension I TR M⟩

theorem r4HilbertCompletionFinal_map_ready_bundle
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMapReady ∧ M.objectMapRespectsQuotientReady ∧
      M.objectMapHandoffReady ∧ M.objectMapCanonicalReady :=
  ⟨r4HilbertCompletionObjectCanonicalMap_ready I TR M,
    r4HilbertCompletionObjectCanonicalMap_respects_quotient_ready I TR M,
    r4HilbertCompletionObjectCanonicalMap_handoff_ready I TR M,
    r4HilbertCompletionObjectCanonicalMap_canonical_ready I TR M⟩

theorem r4HilbertCompletionFinal_readiness_bundle
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMetricReady ∧ M.objectUniformReady ∧ M.objectCauchyReady ∧
      M.objectCompleteReady ∧ M.objectDenseRangeReady ∧ M.objectSeparatedReady :=
  ⟨r4HilbertCompletionReadiness_metric I TR M,
    r4HilbertCompletionReadiness_uniform I TR M,
    r4HilbertCompletionReadiness_cauchy I TR M,
    r4HilbertCompletionReadiness_complete I TR M,
    r4HilbertCompletionReadiness_dense I TR M,
    r4HilbertCompletionReadiness_separated I TR M⟩

theorem r4HilbertCompletionFinal_boundary_bundle
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectBoundaryOpen ∧ M.objectHandoffReady ∧
      M.objectDenseStatementOpen ∧ M.objectCompleteStatementOpen :=
  ⟨r4HilbertCompletionReadiness_boundary I TR M,
    r4HilbertCompletionReadiness_handoff I TR M,
    r4HilbertCompletionReadiness_dense_statement I TR M,
    r4HilbertCompletionReadiness_complete_statement I TR M⟩

theorem r4HilbertCompletionFinal_extension_bundle
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectTransportExtensionReady ∧ M.objectSectionExtensionReady ∧
      M.objectNextLayerReady :=
  ⟨r4HilbertCompletionReadiness_transport_extension I TR M,
    r4HilbertCompletionReadiness_section_extension I TR M,
    r4HilbertCompletionReadiness_next_layer I TR M⟩

theorem r4HilbertCompletionFinal_input_readiness_bundle
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionMetricReady ∧ M.inputData.completionUniformReady ∧
      M.inputData.completionCauchyReady ∧ M.inputData.completionCompleteReady ∧
        M.inputData.completionDenseRangeReady :=
  ⟨r4HilbertCompletionReadiness_input_metric I TR M,
    r4HilbertCompletionReadiness_input_uniform I TR M,
    r4HilbertCompletionReadiness_input_cauchy I TR M,
    r4HilbertCompletionReadiness_input_complete I TR M,
    r4HilbertCompletionReadiness_input_dense I TR M⟩

theorem r4HilbertCompletionFinal_input_boundary_bundle
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionBoundaryOpen ∧ M.inputData.completionNextLayerReady :=
  ⟨r4HilbertCompletionReadiness_input_boundary I TR M,
    r4HilbertCompletionReadiness_input_next_layer I TR M⟩

theorem r4HilbertCompletionFinal_quotient_transport_bundle
    (M : R4HilbertCompletionObjectData I TR) (q : quotientCarrier I)
    (h : quotientPairCoordinateRoundTripProp I TR q) :
    (TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q ∧
      TR.forwardTransport (quotientPairQuotientCoord I TR q) = quotientPairRangeCoord I TR q) ∧
      TR.inverseTransport (quotientPairRangeCoord I TR q) = quotientPairQuotientCoord I TR q :=
  ⟨r4HilbertCompletionTransport_quotient_direct_components I TR M q h,
    r4HilbertCompletionTransport_quotient_inverse I TR M q h⟩

theorem r4HilbertCompletionFinal_range_transport_bundle
    (M : R4HilbertCompletionObjectData I TR) (x : selectedSectionRangeCarrier I X)
    (h : rangePairCoordinateRoundTripProp I TR x) :
    (TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x ∧
      TR.inverseTransport (rangePairRangeCoord I TR x) = rangePairQuotientCoord I TR x) ∧
      TR.forwardTransport (rangePairQuotientCoord I TR x) = rangePairRangeCoord I TR x :=
  ⟨r4HilbertCompletionTransport_range_direct_components I TR M x h,
    r4HilbertCompletionTransport_range_forward I TR M x h⟩

theorem r4HilbertCompletionFinal_next_layer_ready
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectNextLayerReady :=
  r4HilbertCompletionReadiness_next_layer I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
