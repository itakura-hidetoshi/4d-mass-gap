import MGAP4D.MathlibAnalytic.R4HilbertCompletionMapAPI
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

theorem r4HilbertCompletionReadiness_metric
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectMetricReady :=
  r4HilbertCompletionObject_metric_ready I TR M

theorem r4HilbertCompletionReadiness_uniform
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectUniformReady :=
  r4HilbertCompletionObject_uniform_ready I TR M

theorem r4HilbertCompletionReadiness_cauchy
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCauchyReady :=
  r4HilbertCompletionObject_cauchy_ready I TR M

theorem r4HilbertCompletionReadiness_complete
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCompleteReady :=
  r4HilbertCompletionObject_complete_ready I TR M

theorem r4HilbertCompletionReadiness_dense
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectDenseRangeReady :=
  r4HilbertCompletionObject_dense_ready I TR M

theorem r4HilbertCompletionReadiness_separated
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectSeparatedReady :=
  r4HilbertCompletionObject_separated_ready I TR M

theorem r4HilbertCompletionReadiness_boundary
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectBoundaryOpen :=
  r4HilbertCompletionObject_boundary_open I TR M

theorem r4HilbertCompletionReadiness_handoff
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectHandoffReady :=
  r4HilbertCompletionObject_handoff_ready I TR M

theorem r4HilbertCompletionReadiness_dense_statement
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectDenseStatementOpen :=
  r4HilbertCompletionObject_dense_statement_open I TR M

theorem r4HilbertCompletionReadiness_complete_statement
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectCompleteStatementOpen :=
  r4HilbertCompletionObject_complete_statement_open I TR M

theorem r4HilbertCompletionReadiness_transport_extension
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectTransportExtensionReady :=
  r4HilbertCompletionObject_transport_extension_ready I TR M

theorem r4HilbertCompletionReadiness_section_extension
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectSectionExtensionReady :=
  r4HilbertCompletionObject_section_extension_ready I TR M

theorem r4HilbertCompletionReadiness_next_layer
    (M : R4HilbertCompletionObjectData I TR) :
    M.objectNextLayerReady :=
  r4HilbertCompletionObject_next_layer_ready I TR M

theorem r4HilbertCompletionReadiness_input_nonempty
    (M : R4HilbertCompletionObjectData I TR) :
    Nonempty (R4HilbertCompletionInputData I TR) :=
  r4HilbertCompletionObject_input_data_nonempty I TR M

theorem r4HilbertCompletionReadiness_input_metric
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionMetricReady :=
  r4HilbertCompletionObject_input_metric_ready I TR M

theorem r4HilbertCompletionReadiness_input_uniform
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionUniformReady :=
  r4HilbertCompletionObject_input_uniform_ready I TR M

theorem r4HilbertCompletionReadiness_input_cauchy
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionCauchyReady :=
  r4HilbertCompletionObject_input_cauchy_ready I TR M

theorem r4HilbertCompletionReadiness_input_complete
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionCompleteReady :=
  r4HilbertCompletionObject_input_complete_ready I TR M

theorem r4HilbertCompletionReadiness_input_dense
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionDenseRangeReady :=
  r4HilbertCompletionObject_input_dense_ready I TR M

theorem r4HilbertCompletionReadiness_input_boundary
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionBoundaryOpen :=
  r4HilbertCompletionObject_input_boundary_open I TR M

theorem r4HilbertCompletionReadiness_input_next_layer
    (M : R4HilbertCompletionObjectData I TR) :
    M.inputData.completionNextLayerReady :=
  r4HilbertCompletionObject_input_next_layer_ready I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
