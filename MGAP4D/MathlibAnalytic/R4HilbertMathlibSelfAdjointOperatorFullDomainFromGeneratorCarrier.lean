import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainFromGeneratorLift
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

/-- Carrier coverage data routed through the generator handoff domain map.

This layer refines the previous generator-lift route by recording the completed
OS semigroup Hilbert carrier point obtained from each generator-domain lift. It
still keeps the final actual-domain membership as explicit route data rather
than claiming a bare theorem from the generator input alone. -/
structure R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData
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
  generatorCarrierForLift :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      r4HilbertOSGeneratorHandoffCarrier I TR hamiltonianInput.generatorData
  generatorCarrier_eq_domainMap :
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      generatorCarrierForLift x =
        r4HilbertOSGeneratorHandoffDomainMap I TR hamiltonianInput.generatorData
          (generatorLiftForCarrier x)
  generatorCarrierCoversActualDomain :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      let _gcarrier := generatorCarrierForLift x
      x ∈ M.mathlibOperator.domain)

/-- The generator carrier supplied by applying the handoff domain map to the
lifted generator-domain element. -/
def r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_lift
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (gcover : R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :
    r4HilbertOSGeneratorHandoffCarrier I TR gcover.hamiltonianInput.generatorData :=
  r4HilbertOSGeneratorHandoffDomainMap I TR gcover.hamiltonianInput.generatorData
    (gcover.generatorLiftForCarrier x)

/-- The recorded generator carrier agrees with the handoff domain-map image. -/
theorem r4HilbertMathlibSelfAdjointOperator_generator_carrier_eq_domain_map
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (gcover : R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :
    gcover.generatorCarrierForLift x =
      r4HilbertMathlibSelfAdjointOperator_generator_carrier_from_lift I TR gcover x := by
  exact gcover.generatorCarrier_eq_domainMap x

/-- Generator-carrier coverage gives the previous generator-lift coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (gcover : R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M :=
  { hamiltonianInput := gcover.hamiltonianInput
    hamiltonianInputReady := gcover.hamiltonianInputReady
    compatibleWithActualOperator := gcover.compatibleWithActualOperator
    elementForCarrier := gcover.elementForCarrier
    generatorLiftForCarrier := gcover.generatorLiftForCarrier
    generatorLift_eq_map := gcover.generatorLift_eq_map
    liftCoversActualDomain := fun x => by
      exact gcover.generatorCarrierCoversActualDomain x }

/-- Generator-carrier coverage gives the element-level Hamiltonian coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (gcover : R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_lift I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier I TR gcover)

/-- Generator-carrier coverage gives pointwise actual-domain coverage. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_generator_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (gcover : R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_generator_lift I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier I TR gcover)

/-- Generator-carrier coverage constructs `FullDomainData`. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_generator_carrier
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (gcover : R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_generator_lift I TR
    (r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier I TR gcover)

/-- A family of generator-carrier coverage data constructs the bounded route family. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_generator_carrier
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_generator_lift I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier I TR
      (gcover M))

/-- Package theorem for the generator-carrier route. -/
theorem r4HilbertMathlibSelfAdjointOperator_generator_carrier_bounded_route_family_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR ∧
      r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR ∧
        (∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
          R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M) := by
  exact r4HilbertMathlibSelfAdjointOperator_generator_lift_bounded_route_family_package I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_generator_lift_from_generator_carrier I TR
      (gcover M))

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
