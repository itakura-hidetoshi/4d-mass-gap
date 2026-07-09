import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDirectBareMDomainPackage
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

/-! Bundle surface for the direct bare-`M` bounded actual endpoint family. -/

/-- A compact direct bundle collecting the route-free bounded actual consequences of bare `M`. -/
structure R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  boundedActualData : R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M
  fullDomainContinuousData :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR
  boundedActualDomainPackage :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualDomainPackage I TR M
  actualDomain_eq_top :
    r4HilbertMathlibSelfAdjointOperator_direct_bare_M_package_actual_domain_eq_top I TR M
  continuousRepresentative_eq_actual :
    r4HilbertMathlibSelfAdjointOperator_direct_bare_M_package_continuous_eq_actual I TR M

/-- Bare actual R4 operator data directly gives the complete bounded actual bundle. -/
def r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bounded_bundle
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle I TR M :=
  { boundedActualData :=
      r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bounded_actual_data I TR M
    fullDomainContinuousData :=
      r4HilbertMathlibSelfAdjointOperator_direct_bare_M_full_domain_continuous_data I TR M
    boundedActualDomainPackage :=
      r4HilbertMathlibSelfAdjointOperator_direct_bare_M_bounded_actual_domain_package I TR M
    actualDomain_eq_top :=
      r4HilbertMathlibSelfAdjointOperator_direct_bare_M_package_actual_domain_eq_top I TR M
    continuousRepresentative_eq_actual :=
      r4HilbertMathlibSelfAdjointOperator_direct_bare_M_package_continuous_eq_actual I TR M }

/-- The bundle exposes the concrete bounded-domain package. -/
def R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle.domainPackage
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (B : R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle I TR M) :=
  B.boundedActualDomainPackage

/-- The bundle exposes the route-free bounded actual data. -/
def R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle.actualData
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (B : R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle I TR M) :=
  B.boundedActualData

/-- The bundle exposes the route-free full-domain continuous data. -/
def R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle.fullDomainData
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (B : R4HilbertMathlibSelfAdjointOperatorDirectBareMBoundedBundle I TR M) :=
  B.fullDomainContinuousData

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
