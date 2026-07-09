import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle
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

/-! Stable endpoints for the direct bare-`M` bounded bundle. -/

/-- Bare `M` gives the direct bounded bundle. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bounded_bundle I TR M

/-- Bare `M` gives the bundle's bounded actual data endpoint. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  (r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle I TR M).actualData

/-- Bare `M` gives the bundle's full-domain continuous data endpoint. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_full_domain_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  (r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle I TR M).fullDomainData

/-- Bare `M` gives the bundle's concrete bounded-domain package endpoint. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_domain_package
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  (r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle I TR M).domainPackage

/-- Bare `M` gives the bundle's actual-domain proof endpoint. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_actual_domain_eq_top
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  (r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle I TR M).actualDomain_eq_top

/-- Bare `M` gives the bundle's continuous-representative equality endpoint. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle_continuous_representative_eq_actual
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  (r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bundle I TR M).continuousRepresentative_eq_actual

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
