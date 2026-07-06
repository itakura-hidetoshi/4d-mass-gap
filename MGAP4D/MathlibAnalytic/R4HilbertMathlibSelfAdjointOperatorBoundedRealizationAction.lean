import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRealizationConsequences
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
# Conditional action formula for a bounded realization of the R4 operator

This file turns the conditional bounded-realization equality from the previous
layer into an evaluation API.

It does not assert that the actual R4 operator is bounded.  Under the explicit
hypothesis that a bounded operator `B` realizes `M.mathlibOperator` as
`B.toPMap p` on a dense submodule `p`, the existing R4 self-adjointness and
bounded-adjoint bridge identify the action of `M.mathlibOperator` with the
bounded adjoint `B.adjoint`.

No spectral measure, spectral projection, positive lower bound, or spectral gap
is asserted here.
-/

/-- Under a bounded realization, every carrier vector is in the domain of the
actual R4 operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_mem_domain
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
      ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
        x ∈ M.mathlibOperator.domain) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro B p hp hB x
  have hDomain : M.mathlibOperator.domain = ⊤ :=
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_domain_eq_top
      I TR M B p hp hB
  rw [hDomain]
  exact Submodule.mem_top

/-- Under a bounded realization, the actual R4 operator acts as the bounded
adjoint on every domain element. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_apply
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
      ∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
        (hx : x ∈ M.mathlibOperator.domain),
        M.mathlibOperator ⟨x, hx⟩ = B.adjoint x) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro B p hp hB x hx
  have hSelf : M.mathlibOperator = B.adjoint.toPMap ⊤ :=
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_toPMap_self_eq_adjoint_toPMap
      I TR M B p hp hB
  have hTop : x ∈ (B.adjoint.toPMap ⊤).domain := by
    simp
  have hApply := (LinearPMap.ext_iff.mp hSelf).2 (hf := hx) (hg := hTop)
  simpa [LinearMap.toPMap_apply] using hApply

/-- Under a bounded realization, the actual R4 operator acts as the bounded
adjoint on the canonical full-domain element supplied by the previous theorem. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_apply_of_mem_domain
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
      (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
        M.mathlibOperator
            ⟨x,
              r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_mem_domain
                I TR M B p hp hB x⟩ =
          B.adjoint x) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  intro B p hp hB x
  exact r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_apply
    I TR M B p hp hB x
    (r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_mem_domain
      I TR M B p hp hB x)

/-- Conditional package bundling domain membership and the action formula. -/
theorem r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_action_package
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
      (∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
        x ∈ M.mathlibOperator.domain) ∧
        (∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
          (hx : x ∈ M.mathlibOperator.domain),
          M.mathlibOperator ⟨x, hx⟩ = B.adjoint x)) := by
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
  exact ⟨r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_mem_domain
      I TR M B p hp hB,
    r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_apply
      I TR M B p hp hB⟩

/-- This action formula is conditional infrastructure, not a spectral-gap assertion. -/
def r4HilbertMathlibSelfAdjointOperatorBoundedRealizationActionButNoGapAssertion
    (_M : R4HilbertMathlibSelfAdjointOperatorData I TR) : Prop := True

theorem r4HilbertMathlibSelfAdjointOperatorBoundedRealizationActionButNoGapAssertion_holds
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertMathlibSelfAdjointOperatorBoundedRealizationActionButNoGapAssertion I TR M :=
  trivial

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
