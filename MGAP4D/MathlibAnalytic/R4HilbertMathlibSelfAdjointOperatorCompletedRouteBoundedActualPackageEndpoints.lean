import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainContinuousDataFromCompletedRoutes
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

/-! Bounded actual package endpoints from completed and quotient routes. -/

/-- Quotient-carrier coverage directly closes the full bounded actual package. -/
def r4HilbertMathlibSelfAdjointOperator_quotient_carrier_to_full_domain_continuous_bounded_actual_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (qcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorQuotientCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  let FD :=
    r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_quotient_carrier
      I TR hBridge qcover M
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR FD

/-- Completed-OS-carrier coverage directly closes the full bounded actual package. -/
def r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_to_full_domain_continuous_bounded_actual_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (oscover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  let FD :=
    r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_completed_os_carrier
      I TR hBridge oscover M
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR FD

/-- Completed-Hilbert-carrier coverage directly closes the full bounded actual package. -/
def r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_to_full_domain_continuous_bounded_actual_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (hcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  let FD :=
    r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_completed_hilbert_carrier
      I TR hBridge hcover M
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR FD

/-- Completed-pre-carrier coverage directly closes the full bounded actual package. -/
def r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_to_full_domain_continuous_bounded_actual_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (pcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedPreCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  let FD :=
    r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_completed_pre_carrier
      I TR hBridge pcover M
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR FD

/-- Quotient-carrier coverage directly gives bounded actual data through the
full-domain continuous operator data layer. -/
def r4HilbertMathlibSelfAdjointOperator_quotient_carrier_to_full_domain_continuous_bounded_actual_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (qcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorQuotientCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_to_bounded_actual_data I TR
    (r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_quotient_carrier
      I TR hBridge qcover M)

/-- Completed-pre-carrier coverage directly gives bounded actual data through the
full-domain continuous operator data layer. -/
def r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_to_full_domain_continuous_bounded_actual_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (pcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedPreCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_to_bounded_actual_data I TR
    (r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_completed_pre_carrier
      I TR hBridge pcover M)

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
