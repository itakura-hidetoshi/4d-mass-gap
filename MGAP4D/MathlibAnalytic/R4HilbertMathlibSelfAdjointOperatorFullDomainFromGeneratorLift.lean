import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamilyFromHamiltonianCoverage
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

/-- Carrier coverage data routed through the Hamiltonian-to-generator map. -/
structure R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  hamiltonianInput : R4HilbertHamiltonianInputData I TR
  hamiltonianInputReady : hamiltonianInput.hamiltonianInputReady
  compatibleWithActualOperator : M.mathlibOperatorCompatibleWithHamiltonianInput
  elementForCarrier :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      hamiltonianInput.hamiltonianDomain
  generatorLiftForCarrier :
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      r4HilbertOSGeneratorHandoffDomain I TR hamiltonianInput.generatorData
  generatorLift_eq_map :
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      generatorLiftForCarrier x =
        hamiltonianInput.hamiltonianDomainToGeneratorDomain (elementForCarrier x)
  liftCoversActualDomain :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      x ∈ M.mathlibOperator.domain)

/-- Generator-lift coverage gives the element-level Hamiltonian coverage layer. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_lift
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (GL : R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M :=
  { hamiltonianInput := GL.hamiltonianInput
    hamiltonianInputReady := GL.hamiltonianInputReady
    compatibleWithActualOperator := GL.compatibleWithActualOperator
    elementForCarrier := GL.elementForCarrier
    elementCoversCarrier := fun x => GL.liftCoversActualDomain x }

/-- Generator-lift coverage gives pointwise actual-domain coverage. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_generator_lift
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (GL : R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_elements I TR
    (r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_lift I TR GL)

/-- Generator-lift coverage constructs `FullDomainData`. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_generator_lift
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (GL : R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_coverage I TR
    (r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_generator_lift I TR GL)

/-- A family of generator-lift coverage data constructs the bounded route family. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_generator_lift
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (GL : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_hamiltonian_elements I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_lift I TR (GL M))

/-- Package theorem for the generator-lift route. -/
theorem r4HilbertMathlibSelfAdjointOperator_generator_lift_bounded_route_family_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (GL : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR ∧
      r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR ∧
        (∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
          R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M) := by
  exact r4HilbertMathlibSelfAdjointOperator_hamiltonian_element_bounded_route_family_package I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_hamiltonian_elements_from_generator_lift I TR (GL M))

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
