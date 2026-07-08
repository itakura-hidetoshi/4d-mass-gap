import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorCompleteRouteBackedAccessors
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

/-! Route-backed bounded actual endpoints. -/

/-- Generator-carrier coverage gives bounded actual data and full actual domain for bare `M`. -/
theorem r4HilbertMathlibSelfAdjointOperator_generator_carrier_accessor_bounded_actual_endpoints
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) := by
  exact ⟨
    ⟨r4HilbertMathlibSelfAdjointOperator_generator_carrier_accessor_bounded_actual_data I TR
      hBridge gcover M⟩,
    r4HilbertMathlibSelfAdjointOperator_generator_carrier_accessor_actual_domain_eq_top I TR
      hBridge gcover M⟩

/-- Quotient-carrier coverage gives bounded actual data and full actual domain for bare `M`. -/
theorem r4HilbertMathlibSelfAdjointOperator_quotient_carrier_accessor_bounded_actual_endpoints
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (qcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorQuotientCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) := by
  exact ⟨
    ⟨r4HilbertMathlibSelfAdjointOperator_quotient_carrier_accessor_bounded_actual_data I TR
      hBridge qcover M⟩,
    r4HilbertMathlibSelfAdjointOperator_quotient_carrier_accessor_actual_domain_eq_top I TR
      hBridge qcover M⟩

/-- Completed-OS-carrier coverage gives bounded actual data and full actual domain for bare `M`. -/
theorem r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_accessor_bounded_actual_endpoints
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (oscover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) := by
  exact ⟨
    ⟨r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_accessor_bounded_actual_data I TR
      hBridge oscover M⟩,
    r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_accessor_actual_domain_eq_top I TR
      hBridge oscover M⟩

/-- Completed-Hilbert-carrier coverage gives bounded actual data and full actual domain for bare `M`. -/
theorem r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_accessor_bounded_actual_endpoints
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (hcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) := by
  exact ⟨
    ⟨r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_accessor_bounded_actual_data I TR
      hBridge hcover M⟩,
    r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_accessor_actual_domain_eq_top I TR
      hBridge hcover M⟩

/-- Completed-pre-carrier coverage gives bounded actual data and full actual domain for bare `M`. -/
theorem r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_accessor_bounded_actual_endpoints
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (pcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedPreCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) := by
  exact ⟨
    ⟨r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_accessor_bounded_actual_data I TR
      hBridge pcover M⟩,
    r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_accessor_actual_domain_eq_top I TR
      hBridge pcover M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
