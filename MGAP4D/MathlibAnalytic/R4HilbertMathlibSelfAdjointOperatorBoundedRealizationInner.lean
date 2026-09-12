import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRealizationAction
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
# Conditional inner-product formula for a bounded realization of the R4 operator

This file continues the conditional bounded-realization route.

Under the explicit hypothesis that a bounded operator `B` realizes the actual R4
operator as `B.toPMap p = M.mathlibOperator` on a dense submodule `p`, the action
formula from the previous layer and the mathlib bounded-adjoint identity give an
inner-product formula for the actual R4 operator.

No boundedness of the actual R4 operator is asserted without the realization
hypothesis.  No spectral measure, spectral projection, positive lower bound, or
spectral gap is asserted here.
-/

/-- Under a bounded realization, the actual R4 operator satisfies the bounded
adjoint inner-product identity. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_inner_left
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
      ∀ (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
        (hx : x ∈ M.mathlibOperator.domain),
        inner ℝ (M.mathlibOperator ⟨x, hx⟩) y = inner ℝ x (B y)) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro B p hp hB x y hx
  calc
    inner ℝ (M.mathlibOperator ⟨x, hx⟩) y = inner ℝ (B.adjoint x) y := by
      rw [r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_apply
        I TR M B p hp hB x hx]
    _ = inner ℝ x (B y) := by
      simpa using (ContinuousLinearMap.adjoint_inner_left (A := B) y x)

/-- Under a bounded realization, the canonical full-domain element satisfies the
bounded adjoint inner-product identity. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_inner_left_of_mem_domain
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
      (p : Submodule ℝ (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData))
      (hp : Dense (p : Set (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)))
      (hB : B.toPMap p = M.mathlibOperator)
      (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
        inner ℝ
          (M.mathlibOperator
            ⟨x,
              r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_mem_domain
                I TR M B p hp hB x⟩)
          y = inner ℝ x (B y)) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro B p hp hB x y
  exact r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_inner_left
    I TR M B p hp hB x y
    (r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_mem_domain
      I TR M B p hp hB x)

/-- Conditional package bundling the action formula and inner-product formula. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_inner_package
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
      (∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
        (hx : x ∈ M.mathlibOperator.domain),
        M.mathlibOperator ⟨x, hx⟩ = B.adjoint x) ∧
        (∀ (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
          (hx : x ∈ M.mathlibOperator.domain),
          inner ℝ (M.mathlibOperator ⟨x, hx⟩) y = inner ℝ x (B y))) := by
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
  exact ⟨r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_apply
      I TR M B p hp hB,
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_inner_left
      I TR M B p hp hB⟩

/-- This inner-product formula is conditional infrastructure, not a spectral-gap assertion. -/
def r4HilbertMathlibSelfAdjointOperatorBoundedRealizationInnerButNoGapAssertion
    (_M : R4HilbertMathlibSelfAdjointOperatorData I TR) : Prop := True

theorem r4HilbertMathlibSelfAdjointOperatorBoundedRealizationInnerButNoGapAssertion_holds
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertMathlibSelfAdjointOperatorBoundedRealizationInnerButNoGapAssertion I TR M :=
  trivial

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
