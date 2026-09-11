import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorActualToolkit
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

/-!
# Adjoint evaluation for the actual R4 mathlib self-adjoint operator

This file specializes the dense-domain adjoint evaluation API to the actual R4
mathlib operator object `M.mathlibOperator`.

It records the adjoint application formula, the `adjointAux` inner-product
identity, uniqueness of `adjointAux`, and the adjoint application equality
criterion for the R4 operator.

This remains unbounded-operator infrastructure.  It does not assert a spectral
measure, spectral projection, positive lower bound, or spectral gap.
-/

/-- Actual dense-domain adjoint application formula for the R4 operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_adjoint_apply_of_dense
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
    ∀ y : (LinearPMap.adjoint M.mathlibOperator).domain,
      LinearPMap.adjoint M.mathlibOperator y =
        LinearPMap.adjointAux
          (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro y
  exact LinearPMapAdjointToolkit.linearPMap_adjoint_apply_of_dense_invoked
    (T := M.mathlibOperator)
    (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y

/-- Actual `adjointAux` inner-product identity for the R4 operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_adjointAux_inner
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
    ∀ (y : (LinearPMap.adjoint M.mathlibOperator).domain)
      (x : M.mathlibOperator.domain),
      inner ℝ
        (LinearPMap.adjointAux
          (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y) x =
        inner ℝ (y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
          (M.mathlibOperator x)) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro y x
  exact LinearPMapAdjointToolkit.linearPMap_adjointAux_inner_invoked
    (T := M.mathlibOperator)
    (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y x

/-- Actual `adjointAux` uniqueness criterion for the R4 operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_adjointAux_unique
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
    ∀ (y : (LinearPMap.adjoint M.mathlibOperator).domain)
      {x₀ : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData},
      (∀ x : M.mathlibOperator.domain,
        inner ℝ x₀ x =
          inner ℝ (y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
            (M.mathlibOperator x)) →
      LinearPMap.adjointAux
          (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y = x₀) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro y x₀ hx₀
  exact LinearPMapAdjointToolkit.linearPMap_adjointAux_unique_invoked
    (T := M.mathlibOperator)
    (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y hx₀

/-- Actual adjoint application equality criterion for the R4 operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_adjoint_apply_eq
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
    ∀ (y : (LinearPMap.adjoint M.mathlibOperator).domain)
      {x₀ : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData},
      (∀ x : M.mathlibOperator.domain,
        inner ℝ x₀ x =
          inner ℝ (y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
            (M.mathlibOperator x)) →
      LinearPMap.adjoint M.mathlibOperator y = x₀) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro y x₀ hx₀
  exact LinearPMapAdjointToolkit.linearPMap_adjoint_apply_eq_invoked
    (T := M.mathlibOperator)
    (r4HilbertMathlibSelfAdjointOperator_actual_dense_domain I TR M) y hx₀

/-- These adjoint-evaluation facts remain operator infrastructure, not a spectral-gap assertion. -/
def r4HilbertMathlibSelfAdjointOperatorAdjointEvaluationButNoGapAssertion
    (_M : R4HilbertMathlibSelfAdjointOperatorData I TR) : Prop := True

theorem r4HilbertMathlibSelfAdjointOperatorAdjointEvaluationButNoGapAssertion_holds
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertMathlibSelfAdjointOperatorAdjointEvaluationButNoGapAssertion I TR M :=
  trivial

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
