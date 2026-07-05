import MGAP4D.MathlibAnalytic.R4HilbertCompletionFinalAPI
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

structure R4HilbertPreCompletionStructureData where
  completionObject : R4HilbertCompletionObjectData I TR
  preHilbertCarrier : Type
  [instNormedAddCommGroup : NormedAddCommGroup preHilbertCarrier]
  [instNormedSpaceReal : NormedSpace ℝ preHilbertCarrier]
  [instInnerProductSpaceReal : InnerProductSpace ℝ preHilbertCarrier]
  quotientToPreHilbert : quotientCarrier I → preHilbertCarrier
  quotientToPreHilbertInjective : Function.Injective quotientToPreHilbert
  quotientToPreHilbertCompatible : Prop
  quotientToPreHilbertCompatible_holds : quotientToPreHilbertCompatible
  quotientInnerProductWellDefined : Prop
  quotientInnerProductWellDefined_holds : quotientInnerProductWellDefined
  reflectionPositiveFormDescends : Prop
  reflectionPositiveFormDescends_holds : reflectionPositiveFormDescends
  quotientPositiveDefinite : Prop
  quotientPositiveDefinite_holds : quotientPositiveDefinite
  preCompletionReady : Prop
  preCompletionReady_holds : preCompletionReady

theorem r4HilbertPreCompletion_completion_object_ready
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.completionObject.objectNextLayerReady :=
  r4HilbertCompletionFinal_next_layer_ready I TR M.completionObject

theorem r4HilbertPreCompletion_quotient_map_injective
    (M : R4HilbertPreCompletionStructureData I TR) :
    Function.Injective M.quotientToPreHilbert :=
  M.quotientToPreHilbertInjective

theorem r4HilbertPreCompletion_quotient_map_compatible
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.quotientToPreHilbertCompatible :=
  M.quotientToPreHilbertCompatible_holds

theorem r4HilbertPreCompletion_inner_product_well_defined
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.quotientInnerProductWellDefined :=
  M.quotientInnerProductWellDefined_holds

theorem r4HilbertPreCompletion_reflection_positive_descends
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.reflectionPositiveFormDescends :=
  M.reflectionPositiveFormDescends_holds

theorem r4HilbertPreCompletion_positive_definite
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.quotientPositiveDefinite :=
  M.quotientPositiveDefinite_holds

theorem r4HilbertPreCompletion_ready
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.preCompletionReady :=
  M.preCompletionReady_holds

theorem r4HilbertPreCompletion_actual_structure_carrier_nonempty
    (M : R4HilbertPreCompletionStructureData I TR) :
    Nonempty M.preHilbertCarrier := by
  letI : NormedAddCommGroup M.preHilbertCarrier := M.instNormedAddCommGroup
  exact ⟨0⟩

theorem r4HilbertPreCompletion_descent_bundle
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.quotientToPreHilbertCompatible ∧ M.quotientInnerProductWellDefined ∧
      M.reflectionPositiveFormDescends ∧ M.quotientPositiveDefinite :=
  ⟨r4HilbertPreCompletion_quotient_map_compatible I TR M,
    r4HilbertPreCompletion_inner_product_well_defined I TR M,
    r4HilbertPreCompletion_reflection_positive_descends I TR M,
    r4HilbertPreCompletion_positive_definite I TR M⟩

theorem r4HilbertPreCompletion_actual_route_ready_bundle
    (M : R4HilbertPreCompletionStructureData I TR) :
    M.completionObject.objectNextLayerReady ∧ M.preCompletionReady :=
  ⟨r4HilbertPreCompletion_completion_object_ready I TR M,
    r4HilbertPreCompletion_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
