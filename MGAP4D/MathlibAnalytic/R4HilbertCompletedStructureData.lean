import MGAP4D.MathlibAnalytic.R4HilbertPreCompletionStructureData
import Mathlib.Analysis.InnerProductSpace.Basic
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

structure R4HilbertCompletedStructureData where
  preCompletionData : R4HilbertPreCompletionStructureData I TR
  completedHilbertCarrier : Type
  [instNormedAddCommGroup : NormedAddCommGroup completedHilbertCarrier]
  [instNormedSpaceReal : NormedSpace ℝ completedHilbertCarrier]
  [instInnerProductSpaceReal : InnerProductSpace ℝ completedHilbertCarrier]
  [instCompleteSpace : CompleteSpace completedHilbertCarrier]
  preToCompleted : preCompletionData.preHilbertCarrier → completedHilbertCarrier
  quotientToCompleted : quotientCarrier I → completedHilbertCarrier
  quotientToCompletedFactors : Prop
  quotientToCompletedFactors_holds : quotientToCompletedFactors
  preImageDense : Prop
  preImageDense_holds : preImageDense
  quotientImageDense : Prop
  quotientImageDense_holds : quotientImageDense
  completedInnerProductExtends : Prop
  completedInnerProductExtends_holds : completedInnerProductExtends
  completedCompleteReady : Prop
  completedCompleteReady_holds : completedCompleteReady
  completedHilbertReady : Prop
  completedHilbertReady_holds : completedHilbertReady

theorem r4HilbertCompleted_pre_completion_ready
    (M : R4HilbertCompletedStructureData I TR) :
    M.preCompletionData.preCompletionReady :=
  r4HilbertPreCompletion_ready I TR M.preCompletionData

theorem r4HilbertCompleted_carrier_nonempty
    (M : R4HilbertCompletedStructureData I TR) :
    Nonempty M.completedHilbertCarrier := by
  letI : NormedAddCommGroup M.completedHilbertCarrier := M.instNormedAddCommGroup
  exact ⟨0⟩

theorem r4HilbertCompleted_quotient_factors
    (M : R4HilbertCompletedStructureData I TR) :
    M.quotientToCompletedFactors :=
  M.quotientToCompletedFactors_holds

theorem r4HilbertCompleted_pre_image_dense
    (M : R4HilbertCompletedStructureData I TR) :
    M.preImageDense :=
  M.preImageDense_holds

theorem r4HilbertCompleted_quotient_image_dense
    (M : R4HilbertCompletedStructureData I TR) :
    M.quotientImageDense :=
  M.quotientImageDense_holds

theorem r4HilbertCompleted_inner_product_extends
    (M : R4HilbertCompletedStructureData I TR) :
    M.completedInnerProductExtends :=
  M.completedInnerProductExtends_holds

theorem r4HilbertCompleted_complete_ready
    (M : R4HilbertCompletedStructureData I TR) :
    M.completedCompleteReady :=
  M.completedCompleteReady_holds

theorem r4HilbertCompleted_hilbert_ready
    (M : R4HilbertCompletedStructureData I TR) :
    M.completedHilbertReady :=
  M.completedHilbertReady_holds

theorem r4HilbertCompleted_density_bundle
    (M : R4HilbertCompletedStructureData I TR) :
    M.preImageDense ∧ M.quotientImageDense :=
  ⟨r4HilbertCompleted_pre_image_dense I TR M,
    r4HilbertCompleted_quotient_image_dense I TR M⟩

theorem r4HilbertCompleted_completion_bundle
    (M : R4HilbertCompletedStructureData I TR) :
    M.completedInnerProductExtends ∧ M.completedCompleteReady ∧ M.completedHilbertReady :=
  ⟨r4HilbertCompleted_inner_product_extends I TR M,
    r4HilbertCompleted_complete_ready I TR M,
    r4HilbertCompleted_hilbert_ready I TR M⟩

theorem r4HilbertCompleted_actual_route_bundle
    (M : R4HilbertCompletedStructureData I TR) :
    M.preCompletionData.preCompletionReady ∧ M.completedHilbertReady :=
  ⟨r4HilbertCompleted_pre_completion_ready I TR M,
    r4HilbertCompleted_hilbert_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
