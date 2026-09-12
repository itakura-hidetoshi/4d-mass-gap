import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainFromCompletedOSCarrier
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

/-- Completed Hilbert handoff carrier coverage data attached to the completed OS
carrier route.

This layer records a completed Hilbert-space handoff carrier point for each
mathlib self-adjoint carrier vector while inheriting the actual-domain and
bounded-route path from the completed-OS-carrier route. -/
structure R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  completedOSCarrierData :
    R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M
  completedHilbertCarrierForLift :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      r4HilbertCompletedHilbertSpaceHandoffCarrier I TR
        completedOSCarrierData.generatorCarrierData.hamiltonianInput.generatorData.semigroupData.handoffData
  completedHilbertCarrierCoversActualDomain :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      let _completedHilbertCarrier := completedHilbertCarrierForLift x
      x ∈ M.mathlibOperator.domain)

/-- Completed-Hilbert-carrier coverage gives the completed-OS-carrier coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_from_completed_hilbert_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (hcover : R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M :=
  hcover.completedOSCarrierData

/-- A family of completed-Hilbert-carrier coverage data constructs the bounded route family. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_completed_hilbert_carrier
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (hcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_completed_os_carrier I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_from_completed_hilbert_carrier I TR
      (hcover M))

/-- Package theorem for the completed-Hilbert-carrier route. -/
theorem r4HilbertMathlibSelfAdjointOperator_completed_hilbert_carrier_bounded_route_family_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (hcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedHilbertCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR ∧
      r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR ∧
        (∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
          R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M) := by
  exact r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_bounded_route_family_package I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_from_completed_hilbert_carrier I TR
      (hcover M))

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
