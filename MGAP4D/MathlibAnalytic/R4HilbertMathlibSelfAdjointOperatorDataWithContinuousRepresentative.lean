import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual
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

/-! Continuous representative projections from enriched bounded operator data. -/

/-- The continuous representative carried by enriched bounded operator data. -/
def r4HilbertMathlibSelfAdjointOperator_enriched_continuous_representative
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData →L[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
  M.boundedActualData.continuousRepresentative

/-- The enriched continuous representative realizes the actual R4 operator on top. -/
theorem r4HilbertMathlibSelfAdjointOperator_enriched_continuous_representative_eq_actual
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    (r4HilbertMathlibSelfAdjointOperator_enriched_continuous_representative I TR M).toPMap ⊤ =
      M.operatorData.mathlibOperator) :=
  M.boundedActualData.continuousRepresentative_eq_actual

/-- Enriched bounded data makes the actual R4 operator full-domain. -/
theorem r4HilbertMathlibSelfAdjointOperator_enriched_actual_domain_eq_top
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    M.operatorData.mathlibOperator.domain = ⊤) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
  have hEq :=
    r4HilbertMathlibSelfAdjointOperator_enriched_continuous_representative_eq_actual I TR M
  rw [← hEq]
  simp

/-- Every carrier vector lies in the actual R4 operator domain for enriched data. -/
theorem r4HilbertMathlibSelfAdjointOperator_enriched_actual_domain_covers_carrier
    (M : R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData,
      x ∈ M.operatorData.mathlibOperator.domain) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.operatorData.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.operatorData.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.operatorData.selfAdjointnessData
  intro x
  have hTop := r4HilbertMathlibSelfAdjointOperator_enriched_actual_domain_eq_top I TR M
  rw [hTop]
  trivial

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
