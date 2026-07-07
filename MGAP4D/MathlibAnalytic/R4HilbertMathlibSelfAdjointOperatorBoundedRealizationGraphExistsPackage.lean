import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRealizationConsequences
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRealizationInnerActionExistsPackage
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

/-! Graph package for conditional bounded realizations. -/

theorem r4HilbertMathlibSelfAdjointOperator_actual_exists_bounded_realization_graph_package
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
    (∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
        (p : Submodule ℝ (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)),
      Dense (p : Set (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)) ∧
        B.toPMap p = M.mathlibOperator) →
    M.mathlibOperator.domain = ⊤ ∧
      ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
            r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
        B.toPMap ⊤ = M.mathlibOperator ∧ B.adjoint = B ∧
          M.mathlibOperator.graph = (B.toPMap ⊤).graph ∧
          M.mathlibOperator.graph = (B.adjoint.toPMap ⊤).graph ∧
          (∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
            x ∈ M.mathlibOperator.domain) ∧
          (∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
              (hx : x ∈ M.mathlibOperator.domain),
            M.mathlibOperator ⟨x, hx⟩ = B x) ∧
          (∀ (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
              (hx : x ∈ M.mathlibOperator.domain),
            inner ℝ (M.mathlibOperator ⟨x, hx⟩) y = inner ℝ x (B y)) ∧
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
  intro hExists
  rcases hExists with ⟨B, p, hp, hB⟩
  have hInnerPackage :=
    r4HilbertMathlibSelfAdjointOperator_actual_exists_bounded_realization_inner_action_package
      I TR M ⟨B, p, hp, hB⟩
  rcases hInnerPackage with
    ⟨hDomain, B, hTop, hAdjEq, hMem, hAction, hActualInner, hInner⟩
  have hGraphTop : M.mathlibOperator.graph = (B.toPMap ⊤).graph :=
    (congrArg (fun T => T.graph) hTop).symm
  have hGraphAdj : M.mathlibOperator.graph = (B.adjoint.toPMap ⊤).graph := by
    simpa using
      (r4HilbertMathlibSelfAdjointOperator_actual_bounded_realization_graph_eq_adjoint_toPMap_graph
        I TR M B p hp hB)
  exact ⟨hDomain, B, hTop, hAdjEq, hGraphTop, hGraphAdj,
    hMem, hAction, hActualInner, hInner⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
