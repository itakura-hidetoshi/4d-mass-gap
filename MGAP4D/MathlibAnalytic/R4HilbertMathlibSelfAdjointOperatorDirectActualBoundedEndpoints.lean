import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorDataBoundedActualAccessors
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

/-! Direct boundedness endpoints for canonical actual R4 operator data. -/

/-- Bare actual R4 operator data gives bounded actual data with no route witness. -/
def r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  R4HilbertMathlibSelfAdjointOperatorData.boundedActualData I TR M

/-- Bare actual R4 operator data gives enriched bounded-actual operator data. -/
def r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_operator_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  R4HilbertMathlibSelfAdjointOperatorData.boundedActualOperatorData I TR M

/-- Bare actual R4 operator data gives enriched full-domain continuous data. -/
def r4HilbertMathlibSelfAdjointOperator_bare_M_full_domain_continuous_data
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  R4HilbertMathlibSelfAdjointOperatorData.fullDomainContinuousData I TR M

/-- Statement saying the actual bare operator has full domain. -/
def r4HilbertMathlibSelfAdjointOperatorBareMActualDomainStatement
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) : Prop :=
  (letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  M.mathlibOperator.domain = ⊤)

/-- Bare actual R4 operator data gives full actual domain with no route witness. -/
theorem r4HilbertMathlibSelfAdjointOperator_bare_M_actual_domain_eq_top
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertMathlibSelfAdjointOperatorBareMActualDomainStatement I TR M :=
  r4HilbertMathlibSelfAdjointOperator_actualDomain_eq_top I TR M

/-- Bare actual R4 operator data gives a continuous full-domain representative. -/
def r4HilbertMathlibSelfAdjointOperator_bare_M_continuous_representative
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  M.continuousRepresentative

/-- Statement saying the continuous representative realizes the actual operator on `⊤`. -/
def r4HilbertMathlibSelfAdjointOperatorBareMContinuousRepresentativeEqActualStatement
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) : Prop :=
  (letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  (r4HilbertMathlibSelfAdjointOperator_bare_M_continuous_representative I TR M).toPMap ⊤ =
    M.mathlibOperator)

/-- The bare continuous representative realizes the actual R4 operator on `⊤`. -/
theorem r4HilbertMathlibSelfAdjointOperator_bare_M_continuous_representative_eq_actual
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertMathlibSelfAdjointOperatorBareMContinuousRepresentativeEqActualStatement I TR M :=
  M.continuousRepresentative_eq_actual

/-- Bare actual R4 operator data gives the full bounded actual package. -/
def r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_package
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  R4HilbertMathlibSelfAdjointOperatorData.boundedActualPackage I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
