import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedRoutePackage
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

/-! Full bounded actual package from the unconditional bounded route. -/

/-- The unconditional bounded route yields the full bounded actual package for each
actual R4 mathlib self-adjoint operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_unconditional_route_to_bounded_actual_package
    (hRoute : r4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedRoute I TR)
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
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
      B.toPMap ⊤ = M.mathlibOperator ∧
        B.adjoint.toPMap ⊤ = M.mathlibOperator ∧
        B.toPMap ⊤ = B.adjoint.toPMap ⊤ ∧
        B.adjoint.toPMap ⊤ = B.toPMap ⊤ ∧
        B.adjoint = B ∧
        (B.toPMap ⊤).domain = ⊤ ∧
        (B.adjoint.toPMap ⊤).domain = ⊤ ∧
        M.mathlibOperator.domain = ⊤ ∧
        Dense (M.mathlibOperator.domain : Set
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)) ∧
        M.mathlibOperator.IsClosed ∧
        LinearPMap.adjoint M.mathlibOperator = M.mathlibOperator ∧
        M.mathlibOperator = LinearPMap.adjoint M.mathlibOperator ∧
        (LinearPMap.adjoint M.mathlibOperator).domain = M.mathlibOperator.domain ∧
        (LinearPMap.adjoint M.mathlibOperator).graph = M.mathlibOperator.graph ∧
        M.mathlibOperator.graph = M.mathlibOperator.graph.adjoint ∧
        M.mathlibOperator.graph.adjoint.toLinearPMap = M.mathlibOperator ∧
        M.mathlibOperator.IsFormalAdjoint M.mathlibOperator ∧
        M.mathlibOperator ≤ LinearPMap.adjoint M.mathlibOperator ∧
        LinearPMap.adjoint M.mathlibOperator ≤ M.mathlibOperator ∧
        (B.toPMap ⊤).graph = M.mathlibOperator.graph ∧
        (B.adjoint.toPMap ⊤).graph = M.mathlibOperator.graph ∧
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
  exact r4HilbertMathlibSelfAdjointOperator_bounded_actual_package I TR M
    (r4HilbertMathlibSelfAdjointOperator_unconditional_route_to_bounded_actual_data I TR hRoute M)

/-- Compact summary of the three main consequences of the unconditional bounded
route for a fixed actual R4 operator. -/
theorem r4HilbertMathlibSelfAdjointOperator_unconditional_route_summary_package
    (hRoute : r4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedRoute I TR)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    M.mathlibOperator.domain = ⊤ ∧
      (∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
            r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
        B.toPMap ⊤ = M.mathlibOperator) ∧
      Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M)) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  refine ⟨?_, ?_, ?_⟩
  · exact r4HilbertMathlibSelfAdjointOperator_unconditional_route_domain_eq_top I TR hRoute M
  · exact r4HilbertMathlibSelfAdjointOperator_unconditional_route_top_representative I TR hRoute M
  · exact ⟨r4HilbertMathlibSelfAdjointOperator_unconditional_route_to_bounded_actual_data I TR hRoute M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
