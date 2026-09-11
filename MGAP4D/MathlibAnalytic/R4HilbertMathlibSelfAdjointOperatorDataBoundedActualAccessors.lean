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

/-! Unconditional boundedness accessors on bare actual R4 operator data. -/

namespace R4HilbertMathlibSelfAdjointOperatorData

/-- The bounded actual data carried directly by bare actual R4 operator data. -/
def boundedActualData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  { continuousRepresentative := M.continuousRepresentative
    continuousRepresentative_eq_actual := M.continuousRepresentative_eq_actual }

/-- Enriched bounded actual operator data obtained unconditionally from bare operator data. -/
def boundedActualOperatorData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  { operatorData := M
    boundedActualData := boundedActualData I TR M }

/-- Enriched full-domain continuous operator data obtained unconditionally from bare operator data. -/
def fullDomainContinuousData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  { operatorData := M
    continuousRepresentative := M.continuousRepresentative
    continuousRepresentative_eq_actual := M.continuousRepresentative_eq_actual
    actualDomain_eq_top := M.actualDomain_eq_top }

/-- Field-like accessor to the top-domain representative package. -/
def topRepresentative
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_top_representative I TR
    (fullDomainContinuousData I TR M)

/-- Field-like accessor to the full bounded actual package. -/
def boundedActualPackage
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR
    (fullDomainContinuousData I TR M)

end R4HilbertMathlibSelfAdjointOperatorData

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
