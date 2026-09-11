import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRealizationInnerSymmetric
import Mathlib.Analysis.InnerProductSpace.LinearPMap
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

/-! Package of conditional self-adjoint consequences for a bounded realization. -/

theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_self_adjoint_package
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
    ∀ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
      (p : Submodule ℝ (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)),
      Dense (p : Set (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)) →
      B.toPMap p = M.mathlibOperator →
      p = ⊤ ∧ B.toPMap ⊤ = M.mathlibOperator ∧ B.adjoint = B ∧
        (∀ x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
          inner ℝ (B x) y = inner ℝ x (B y))) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro B p hp hB
  exact ⟨r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_submodule_eq_top
      I TR M B p hp hB,
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_toPMap_top_eq_actual
      I TR M B p hp hB,
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_bounded_adjoint_eq_self
      I TR M B p hp hB,
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_bounded_inner_symmetric
      I TR M B p hp hB⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
