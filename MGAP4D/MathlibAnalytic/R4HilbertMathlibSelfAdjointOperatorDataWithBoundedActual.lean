import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualEndpoints
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

/-! Operator data enriched with bounded actual evidence. -/

/-- Enriched actual R4 mathlib operator data carrying bounded actual data inside the
same record.

This is the constructor-safe version of adding boundedness evidence to
`R4HilbertMathlibSelfAdjointOperatorData`: existing constructors of the base data
are not broken, while downstream code can now choose this enriched data whenever
boundedness must be part of the operator datum itself. -/
structure R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual where
  operatorData : R4HilbertMathlibSelfAdjointOperatorData I TR
  boundedActualData :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR operatorData

/-- Coerce enriched bounded data back to the original actual operator data. -/
instance : Coe
    (R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR)
    (R4HilbertMathlibSelfAdjointOperatorData I TR) where
  coe M := M.operatorData

/-- The bounded actual evidence contained in the enriched datum. -/
def r4HilbertMathlibSelfAdjointOperator_enriched_bounded_actual_data
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M.operatorData :=
  M.boundedActualData

/-- Build enriched data from bare operator data once the central supply is installed. -/
def r4HilbertMathlibSelfAdjointOperator_enrich_with_bounded_actual_data
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR where
  operatorData := M
  boundedActualData :=
    r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_bounded_actual_data I TR M

/-- Enriched data directly supplies the continuous top-domain representative. -/
theorem r4HilbertMathlibSelfAdjointOperator_enriched_top_representative
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData),
      B.toPMap ⊤ = M.operatorData.mathlibOperator) := by
  exact r4HilbertMathlibSelfAdjointOperator_bounded_actual_top_representative I TR
    M.operatorData M.boundedActualData

/-- Enriched data directly supplies the full bounded actual package. -/
theorem r4HilbertMathlibSelfAdjointOperator_enriched_bounded_actual_package
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.operatorData.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData),
      B.toPMap ⊤ = M.operatorData.mathlibOperator ∧
        B.adjoint.toPMap ⊤ = M.operatorData.mathlibOperator ∧
        B.toPMap ⊤ = B.adjoint.toPMap ⊤ ∧
        B.adjoint.toPMap ⊤ = B.toPMap ⊤ ∧
        B.adjoint = B ∧
        (B.toPMap ⊤).domain = ⊤ ∧
        (B.adjoint.toPMap ⊤).domain = ⊤ ∧
        M.operatorData.mathlibOperator.domain = ⊤ ∧
        Dense (M.operatorData.mathlibOperator.domain : Set
          (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData)) ∧
        M.operatorData.mathlibOperator.IsClosed ∧
        LinearPMap.adjoint M.operatorData.mathlibOperator = M.operatorData.mathlibOperator ∧
        M.operatorData.mathlibOperator = LinearPMap.adjoint M.operatorData.mathlibOperator ∧
        (LinearPMap.adjoint M.operatorData.mathlibOperator).domain = M.operatorData.mathlibOperator.domain ∧
        (LinearPMap.adjoint M.operatorData.mathlibOperator).graph = M.operatorData.mathlibOperator.graph ∧
        M.operatorData.mathlibOperator.graph = M.operatorData.mathlibOperator.graph.adjoint ∧
        M.operatorData.mathlibOperator.graph.adjoint.toLinearPMap = M.operatorData.mathlibOperator ∧
        M.operatorData.mathlibOperator.IsFormalAdjoint M.operatorData.mathlibOperator ∧
        M.operatorData.mathlibOperator ≤ LinearPMap.adjoint M.operatorData.mathlibOperator ∧
        LinearPMap.adjoint M.operatorData.mathlibOperator ≤ M.operatorData.mathlibOperator ∧
        (B.toPMap ⊤).graph = M.operatorData.mathlibOperator.graph ∧
        (B.adjoint.toPMap ⊤).graph = M.operatorData.mathlibOperator.graph ∧
        M.operatorData.mathlibOperator.graph = (B.toPMap ⊤).graph ∧
        M.operatorData.mathlibOperator.graph = (B.adjoint.toPMap ⊤).graph ∧
        (∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData,
          x ∈ M.operatorData.mathlibOperator.domain) ∧
        (∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData)
            (hx : x ∈ M.operatorData.mathlibOperator.domain),
          M.operatorData.mathlibOperator ⟨x, hx⟩ = B x) ∧
        (∀ (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData)
            (hx : x ∈ M.operatorData.mathlibOperator.domain),
          inner ℝ (M.operatorData.mathlibOperator ⟨x, hx⟩) y = inner ℝ x (B y)) ∧
        (∀ x y : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData,
          inner ℝ (B x) y = inner ℝ x (B y))) := by
  exact r4HilbertMathlibSelfAdjointOperator_bounded_actual_package I TR
    M.operatorData M.boundedActualData

/-- Enriched data closes the boundedness endpoints without any separate route argument. -/
theorem r4HilbertMathlibSelfAdjointOperator_enriched_boundedness_endpoints
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M.operatorData) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
      ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData →L[ℝ]
            r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData),
        B.toPMap ⊤ = M.operatorData.mathlibOperator) := by
  exact ⟨⟨M.boundedActualData⟩,
    r4HilbertMathlibSelfAdjointOperator_enriched_top_representative I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
