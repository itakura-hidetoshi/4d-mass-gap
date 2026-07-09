import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedActualDomainPackage
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative
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

/-! Conversions from bounded actual domain packages to enriched operator data. -/

/-- Convert a bounded actual domain package into the enriched bounded-actual operator data layer. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_bounded_actual_operator_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR)
    (pkg : R4HilbertMathlibSelfAdjointOperatorBoundedActualDomainPackage I TR M) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  { operatorData := M
    boundedActualData := pkg.boundedActualData }

/-- Convert a bounded actual domain package into the enriched full-domain continuous data layer. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_full_domain_continuous_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR)
    (pkg : R4HilbertMathlibSelfAdjointOperatorBoundedActualDomainPackage I TR M) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  { operatorData := M
    continuousRepresentative := pkg.boundedActualData.continuousRepresentative
    continuousRepresentative_eq_actual := pkg.boundedActualData.continuousRepresentative_eq_actual
    actualDomain_eq_top := pkg.actualDomain_eq_top }

/-- Generator-carrier route constructor into enriched bounded-actual operator data. -/
def r4HilbertMathlibSelfAdjointOperator_generator_carrier_to_bounded_actual_operator_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_bounded_actual_operator_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_generator_carrier_bounded_actual_domain_package I TR
      hBridge gcover M)

/-- Generator-carrier route constructor into enriched full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_generator_carrier_to_full_domain_continuous_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_full_domain_continuous_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_generator_carrier_bounded_actual_domain_package I TR
      hBridge gcover M)

/-- Quotient-carrier route constructor into enriched bounded-actual operator data. -/
def r4HilbertMathlibSelfAdjointOperator_quotient_carrier_to_bounded_actual_operator_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (qcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorQuotientCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_bounded_actual_operator_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_quotient_carrier_bounded_actual_domain_package I TR
      hBridge qcover M)

/-- Quotient-carrier route constructor into enriched full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_quotient_carrier_to_full_domain_continuous_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (qcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorQuotientCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_full_domain_continuous_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_quotient_carrier_bounded_actual_domain_package I TR
      hBridge qcover M)

/-- Completed-OS-carrier route constructor into enriched bounded-actual operator data. -/
def r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_to_bounded_actual_operator_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (oscover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_bounded_actual_operator_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_bounded_actual_domain_package I TR
      hBridge oscover M)

/-- Completed-OS-carrier route constructor into enriched full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_to_full_domain_continuous_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (oscover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_full_domain_continuous_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_bounded_actual_domain_package I TR
      hBridge oscover M)

/-- Completed-Hilbert-carrier route constructor into enriched bounded-actual operator data. -/
def r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_to_bounded_actual_operator_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (hcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_bounded_actual_operator_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_bounded_actual_domain_package I TR
      hBridge hcover M)

/-- Completed-Hilbert-carrier route constructor into enriched full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_to_full_domain_continuous_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (hcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_full_domain_continuous_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_bounded_actual_domain_package I TR
      hBridge hcover M)

/-- Completed-pre-carrier route constructor into enriched bounded-actual operator data. -/
def r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_to_bounded_actual_operator_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (pcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedPreCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_bounded_actual_operator_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_bounded_actual_domain_package I TR
      hBridge pcover M)

/-- Completed-pre-carrier route constructor into enriched full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_to_full_domain_continuous_data
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (pcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedPreCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_domain_package_to_full_domain_continuous_data I TR M
    (r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_bounded_actual_domain_package I TR
      hBridge pcover M)

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
