import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRoute
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

/-! Central bare bounded actual endpoints. -/

/-- With the central supply installed, bare `M` has a continuous top-domain representative. -/
theorem r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_top_representative
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
      B.toPMap ⊤ = M.mathlibOperator) := by
  exact r4HilbertMathlibSelfAdjointOperator_bare_M_top_representative I TR M

/-- With the central supply installed, bare `M` satisfies the full bounded actual package. -/
theorem r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_bounded_actual_package
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
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
  exact r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_package I TR M

/-- With the central supply installed, all bare-`M` bounded actual endpoints are closed. -/
theorem r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_boundedness_endpoints
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
            r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
        B.toPMap ⊤ = M.mathlibOperator) := by
  exact ⟨
    r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_bounded_actual_nonempty I TR M,
    r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_top_representative I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
