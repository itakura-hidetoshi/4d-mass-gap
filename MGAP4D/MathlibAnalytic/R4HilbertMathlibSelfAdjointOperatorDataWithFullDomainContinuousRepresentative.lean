import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDataWithContinuousRepresentative
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

/-! Operator data enriched with explicit full-domain continuous representative evidence. -/

/-- Enriched actual R4 mathlib operator data carrying a continuous representative
and the full-domain equality as fields.

This is the expanded data form of bounded actual evidence: instead of keeping the
witness packaged only as `R4HilbertMathlibSelfAdjointOperatorBoundedActualData`, it
stores the continuous representative, the equality to the actual operator on `⊤`,
and the explicit `domain = ⊤` proof beside the original operator data. -/
structure R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative where
  operatorData : R4HilbertMathlibSelfAdjointOperatorData I TR
  continuousRepresentative :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR operatorData.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData →L[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData)
  continuousRepresentative_eq_actual :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR operatorData.selfAdjointnessData
    continuousRepresentative.toPMap ⊤ = operatorData.mathlibOperator)
  actualDomain_eq_top :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR operatorData.selfAdjointnessData
    operatorData.mathlibOperator.domain = ⊤)

/-- Coerce the full-domain continuous-representative data back to the original
actual operator data. -/
instance : Coe
    (R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR)
    (R4HilbertMathlibSelfAdjointOperatorData I TR) where
  coe M := M.operatorData

/-- Repackage explicit full-domain continuous-representative data as bounded actual data. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_to_bounded_actual_data
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M.operatorData where
  continuousRepresentative := M.continuousRepresentative
  continuousRepresentative_eq_actual := M.continuousRepresentative_eq_actual

/-- Repackage explicit full-domain continuous-representative data as the bounded
actual enriched operator data. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_to_bounded_actual_operator_data
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR where
  operatorData := M.operatorData
  boundedActualData :=
    r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_to_bounded_actual_data I TR M

/-- Expand bounded actual enriched operator data into full-domain continuous-representative data. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_actual_to_full_domain_continuous_operator_data
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR where
  operatorData := M.operatorData
  continuousRepresentative := M.boundedActualData.continuousRepresentative
  continuousRepresentative_eq_actual := M.boundedActualData.continuousRepresentative_eq_actual
  actualDomain_eq_top :=
    r4HilbertMathlibSelfAdjointOperator_enriched_actual_domain_eq_top I TR M

/-- Build full-domain continuous-representative data from bare operator data once
the central supply is installed. -/
def r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_to_full_domain_continuous_operator_data I TR
    (r4HilbertMathlibSelfAdjointOperator_enrich_with_bounded_actual_data I TR M)

/-- The stored continuous representative realizes the actual R4 operator on `⊤`. -/
theorem r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_eq_actual
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    M.continuousRepresentative.toPMap ⊤ = M.operatorData.mathlibOperator) :=
  M.continuousRepresentative_eq_actual

/-- The full-domain proof is stored directly in the enriched data. -/
theorem r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_domain_eq_top
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    M.operatorData.mathlibOperator.domain = ⊤) :=
  M.actualDomain_eq_top

/-- Full-domain continuous-representative data directly gives the top representative. -/
theorem r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_top_representative
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData),
      B.toPMap ⊤ = M.operatorData.mathlibOperator) := by
  exact ⟨M.continuousRepresentative, M.continuousRepresentative_eq_actual⟩

/-- Full-domain continuous-representative data closes the bounded actual package. -/
theorem r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR) :
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
    M.operatorData
    (r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_to_bounded_actual_data I TR M)

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
