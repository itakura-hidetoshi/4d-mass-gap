import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainFromGeneratorCarrier
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

/-- Carrier coverage data with the generator-domain lift rewritten as a completed
OS semigroup Hilbert carrier point.

This is the next internalization step after the generator-carrier route. It makes
explicit that the carrier produced from a generator-domain lift lives in the
completed OS semigroup handoff carrier. The final actual-domain membership is
still recorded as route data. -/
structure R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  hamiltonianInput : R4HilbertHamiltonianInputData I TR
  hamiltonianInputReady : hamiltonianInput.hamiltonianInputReady
  compatibleWithActualOperator : M.mathlibOperatorCompatibleWithHamiltonianInput
  elementForCarrier :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      hamiltonianInput.hamiltonianDomain
  generatorLiftForCarrier :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      r4HilbertOSGeneratorHandoffDomain I TR hamiltonianInput.generatorData
  generatorLift_eq_map :
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      generatorLiftForCarrier x =
        hamiltonianInput.hamiltonianDomainToGeneratorDomain (elementForCarrier x)
  completedOSCarrierForLift :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      r4HilbertCompletedOSSemigroupHandoffCarrier I TR hamiltonianInput.generatorData.semigroupData
  completedOSCarrier_eq_domainMap :
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      completedOSCarrierForLift x =
        r4HilbertOSGeneratorHandoffDomainMap I TR hamiltonianInput.generatorData
          (generatorLiftForCarrier x)
  completedOSCarrierCoversActualDomain :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      let _osCarrier := completedOSCarrierForLift x
      x ∈ M.mathlibOperator.domain)

/-- The completed OS semigroup carrier obtained from a generator-domain lift. -/
def r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_from_lift
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M)
    (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :
    r4HilbertCompletedOSSemigroupHandoffCarrier I TR
      oscover.hamiltonianInput.generatorData.semigroupData :=
  r4HilbertOSGeneratorHandoffDomainMap I TR oscover.hamiltonianInput.generatorData
    (oscover.generatorLiftForCarrier x)

/-- The recorded completed OS carrier agrees with the generator handoff domain-map image. -/
theorem r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_eq_domain_map
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M)
    (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :
    oscover.completedOSCarrierForLift x =
      r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_from_lift I TR oscover x := by
  exact oscover.completedOSCarrier_eq_domainMap x

/-- Completed-OS-carrier coverage gives the generator-carrier coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M :=
  { hamiltonianInput := oscover.hamiltonianInput
    hamiltonianInputReady := oscover.hamiltonianInputReady
    compatibleWithActualOperator := oscover.compatibleWithActualOperator
    elementForCarrier := oscover.elementForCarrier
    generatorLiftForCarrier := oscover.generatorLiftForCarrier
    generatorLift_eq_map := oscover.generatorLift_eq_map
    generatorCarrierForLift := oscover.completedOSCarrierForLift
    generatorCarrier_eq_domainMap := oscover.completedOSCarrier_eq_domainMap
    generatorCarrierCoversActualDomain := fun x => by
      exact oscover.completedOSCarrierCoversActualDomain x }

/-- Completed-OS-carrier coverage gives the previous generator-lift coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_generator_lift_from_completed_os_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier I TR oscover)

/-- Completed-OS-carrier coverage gives the element-level Hamiltonian coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_completed_os_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_carrier I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier I TR oscover)

/-- Completed-OS-carrier coverage gives pointwise actual-domain coverage. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_completed_os_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_generator_carrier I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier I TR oscover)

/-- Completed-OS-carrier coverage constructs `FullDomainData`. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_completed_os_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (oscover : R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_generator_carrier I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier I TR oscover)

/-- A family of completed-OS-carrier coverage data constructs the bounded route family. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_completed_os_carrier
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (oscover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_generator_carrier I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier I TR
      (oscover M))

/-- Package theorem for the completed-OS-carrier route. -/
theorem r4HilbertMathlibSelfAdjointOperator_completed_os_carrier_bounded_route_family_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (oscover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorCompletedOSCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR ∧
      r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR ∧
        (∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
          R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M) := by
  exact r4HilbertMathlibSelfAdjointOperator_generator_carrier_bounded_route_family_package I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_completed_os_carrier I TR
      (oscover M))

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
