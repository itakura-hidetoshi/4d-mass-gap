import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundleEndpoints
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

/-!
Compatibility surface for the old route-backed boundedness API.

After the direct actual R4 operator data refactor, boundedness is carried by bare
`R4HilbertMathlibSelfAdjointOperatorData` itself.  The definitions below keep
route-backed call sites source-compatible while deliberately delegating to the
route-free direct bundle endpoints.
-/

/-- Compatibility endpoint: old route-backed callers should read bounded actual data from bare `M`. -/
def r4HilbertMathlibSelfAdjointOperator_route_backed_compat_bounded_actual_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data I TR M

/-- Compatibility endpoint: old route-backed callers should read full-domain data from bare `M`. -/
def r4HilbertMathlibSelfAdjointOperator_route_backed_compat_full_domain_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data I TR M

/-- Compatibility endpoint: old route-backed callers should read the package from bare `M`. -/
def r4HilbertMathlibSelfAdjointOperator_route_backed_compat_domain_package
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package I TR M

/-- Compatibility endpoint: route arguments are retained only for source compatibility. -/
def r4HilbertMathlibSelfAdjointOperator_generator_carrier_compat_bounded_actual_data
    (_hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (_gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_route_backed_compat_bounded_actual_data I TR M

/-- Compatibility endpoint: route arguments are retained only for source compatibility. -/
def r4HilbertMathlibSelfAdjointOperator_quotient_carrier_compat_bounded_actual_data
    (_hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (_qcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorQuotientCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_route_backed_compat_bounded_actual_data I TR M

/-- Compatibility endpoint: route arguments are retained only for source compatibility. -/
def r4HilbertMathlibSelfAdjointOperator_completed_pre_carrier_compat_bounded_actual_data
    (_hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (_pcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedPreCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_route_backed_compat_bounded_actual_data I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
