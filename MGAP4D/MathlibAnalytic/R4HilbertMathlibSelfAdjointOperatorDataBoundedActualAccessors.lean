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

/-! Field-like boundedness accessors on bare actual R4 operator data. -/

namespace R4HilbertMathlibSelfAdjointOperatorData

/-- Field-like accessor from bare operator data to bounded actual data once the
central bare bounded actual route supply is installed. -/
def boundedActualData
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_bounded_actual_data I TR M

/-- Field-like accessor from bare operator data to enriched bounded actual operator data. -/
def boundedActualOperatorData
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithBoundedActual I TR :=
  r4HilbertMathlibSelfAdjointOperator_enrich_with_bounded_actual_data I TR M

/-- Field-like accessor from bare operator data to full-domain continuous operator data. -/
def fullDomainContinuousData
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR :=
  r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative I TR M

/-- Field-like accessor to the continuous representative carried by the central supply. -/
def continuousRepresentative
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  (boundedActualData I TR M).continuousRepresentative

/-- The field-like continuous representative realizes the actual operator on `⊤`. -/
theorem continuousRepresentative_eq_actual
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    (continuousRepresentative I TR M).toPMap ⊤ = M.mathlibOperator) :=
  (boundedActualData I TR M).continuousRepresentative_eq_actual

/-- Field-like accessor to the full-domain proof for the actual operator. -/
theorem actualDomain_eq_top
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    M.mathlibOperator.domain = ⊤) :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_domain_eq_top I TR
    (fullDomainContinuousData I TR M)

/-- Field-like accessor to the top-domain representative package. -/
def topRepresentative
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_top_representative I TR
    (fullDomainContinuousData I TR M)

/-- Field-like accessor to the full bounded actual package. -/
def boundedActualPackage
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR
    (fullDomainContinuousData I TR M)

end R4HilbertMathlibSelfAdjointOperatorData

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
