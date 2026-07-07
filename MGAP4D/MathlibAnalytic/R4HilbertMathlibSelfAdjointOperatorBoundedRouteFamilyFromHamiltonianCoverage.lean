import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainFromHamiltonianCoverage
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily
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

/-- Data that records a Hamiltonian-domain element for each carrier vector and
then derives the actual-domain coverage from that element-level construction. -/
structure R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  hamiltonianInput : R4HilbertHamiltonianInputData I TR
  hamiltonianInputReady : hamiltonianInput.hamiltonianInputReady
  compatibleWithActualOperator : M.mathlibOperatorCompatibleWithHamiltonianInput
  elementForCarrier :
    ∀ _x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      hamiltonianInput.hamiltonianDomain
  elementCoversCarrier :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      let _h := elementForCarrier x
      x ∈ M.mathlibOperator.domain)

/-- Element-level Hamiltonian coverage yields pointwise actual-domain coverage. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_elements
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (EC : R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M :=
  { hamiltonianInput := EC.hamiltonianInput
    hamiltonianInputReady := EC.hamiltonianInputReady
    compatibleWithActualOperator := EC.compatibleWithActualOperator
    actualDomainCoversCarrier := fun x => by
      simpa using EC.elementCoversCarrier x }

/-- Element-level Hamiltonian coverage constructs the bounded-route `FullDomainData`. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_elements
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (EC : R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_coverage I TR
    (r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_elements I TR EC)

/-- A family of Hamiltonian coverage data, together with the closed-graph bridge,
constructs the bounded route family used by the downstream bounded-operator layer. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_hamiltonian_coverage
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (HC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR :=
  { closedGraphBridge := hBridge
    fullDomainData := fun M =>
      r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_coverage I TR
        (HC M) }

/-- A family of Hamiltonian element-level coverage data, together with the
closed-graph bridge, constructs the bounded route family. -/
def r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_hamiltonian_elements
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (EC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR :=
  r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_hamiltonian_coverage I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_elements I TR (EC M))

/-- Package theorem for the Hamiltonian-coverage route family. -/
theorem r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_bounded_route_family_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (HC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR ∧
      r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR ∧
        (∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
          R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M) := by
  exact ⟨
    r4HilbertMathlibSelfAdjointOperator_bounded_route_family_from_hamiltonian_coverage I TR
      hBridge HC,
    hBridge,
    fun M =>
      r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_coverage I TR
        (HC M)⟩

/-- Package theorem for the Hamiltonian element-level route family. -/
theorem r4HilbertMathlibSelfAdjointOperator_hamiltonian_element_bounded_route_family_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (EC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorBoundedRouteFamily I TR ∧
      r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR ∧
        (∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
          R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M) := by
  exact r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_bounded_route_family_package I TR
    hBridge
    (fun M => r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_from_elements I TR (EC M))

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
