import MGAP4D.MathlibAnalytic.R4HilbertCompletedStructureData
import Mathlib.Topology.Basic
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

structure R4HilbertCompletedDenseRangeData where
  completedData : R4HilbertCompletedStructureData I TR
  preToCompletedDenseActual :
    (letI : NormedAddCommGroup completedData.preCompletionData.preHilbertCarrier :=
      completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup completedData.completedHilbertCarrier :=
      completedData.instNormedAddCommGroup
    DenseRange completedData.preToCompleted)
  quotientToCompletedDenseActual :
    (letI : NormedAddCommGroup completedData.completedHilbertCarrier :=
      completedData.instNormedAddCommGroup
    DenseRange completedData.quotientToCompleted)
  preToCompletedContinuousActual :
    (letI : NormedAddCommGroup completedData.preCompletionData.preHilbertCarrier :=
      completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup completedData.completedHilbertCarrier :=
      completedData.instNormedAddCommGroup
    Continuous completedData.preToCompleted)
  quotientDenseRouteReady : Prop
  quotientDenseRouteReady_holds : quotientDenseRouteReady
  completedDenseRangeReady : Prop
  completedDenseRangeReady_holds : completedDenseRangeReady

theorem r4HilbertCompletedDense_pre_dense_actual
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup M.completedData.preCompletionData.preHilbertCarrier :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup M.completedData.completedHilbertCarrier :=
      M.completedData.instNormedAddCommGroup
    DenseRange M.completedData.preToCompleted) :=
  M.preToCompletedDenseActual

theorem r4HilbertCompletedDense_quotient_dense_actual
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup M.completedData.completedHilbertCarrier :=
      M.completedData.instNormedAddCommGroup
    DenseRange M.completedData.quotientToCompleted) :=
  M.quotientToCompletedDenseActual

theorem r4HilbertCompletedDense_pre_continuous_actual
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup M.completedData.preCompletionData.preHilbertCarrier :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup M.completedData.completedHilbertCarrier :=
      M.completedData.instNormedAddCommGroup
    Continuous M.completedData.preToCompleted) :=
  M.preToCompletedContinuousActual

theorem r4HilbertCompletedDense_quotient_dense_route_ready
    (M : R4HilbertCompletedDenseRangeData I TR) :
    M.quotientDenseRouteReady :=
  M.quotientDenseRouteReady_holds

theorem r4HilbertCompletedDense_completed_dense_ready
    (M : R4HilbertCompletedDenseRangeData I TR) :
    M.completedDenseRangeReady :=
  M.completedDenseRangeReady_holds

theorem r4HilbertCompletedDense_actual_bundle
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup M.completedData.preCompletionData.preHilbertCarrier :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup M.completedData.completedHilbertCarrier :=
      M.completedData.instNormedAddCommGroup
    DenseRange M.completedData.preToCompleted) ∧
      (letI : NormedAddCommGroup M.completedData.completedHilbertCarrier :=
        M.completedData.instNormedAddCommGroup
      DenseRange M.completedData.quotientToCompleted) :=
  ⟨r4HilbertCompletedDense_pre_dense_actual I TR M,
    r4HilbertCompletedDense_quotient_dense_actual I TR M⟩

theorem r4HilbertCompletedDense_route_bundle
    (M : R4HilbertCompletedDenseRangeData I TR) :
    M.quotientDenseRouteReady ∧ M.completedDenseRangeReady :=
  ⟨r4HilbertCompletedDense_quotient_dense_route_ready I TR M,
    r4HilbertCompletedDense_completed_dense_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
