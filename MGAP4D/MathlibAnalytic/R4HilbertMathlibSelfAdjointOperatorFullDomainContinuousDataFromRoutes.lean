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

/-! Direct route constructors for full-domain continuous operator data. -/

/-- Build full-domain continuous-representative data from an explicit bare bounded
actual route. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_bare_bounded_actual_route
    (bareRoute : R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR := by
  letI : R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR :=
    r4HilbertMathlibSelfAdjointOperator_central_supply_from_bare_bounded_actual_route I TR
      bareRoute
  exact r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative I TR M

/-- Build full-domain continuous-representative data from Hamiltonian-domain coverage. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_hamiltonian_coverage
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (HC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR := by
  letI : R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR :=
    r4HilbertMathlibSelfAdjointOperator_central_supply_from_hamiltonian_coverage I TR
      hBridge HC
  exact r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative I TR M

/-- Build full-domain continuous-representative data from Hamiltonian element coverage. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_hamiltonian_elements
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (EC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR := by
  letI : R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR :=
    r4HilbertMathlibSelfAdjointOperator_central_supply_from_hamiltonian_elements I TR
      hBridge EC
  exact r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative I TR M

/-- Build full-domain continuous-representative data from generator-lift coverage. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_generator_lift
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (glift : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR := by
  letI : R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR :=
    r4HilbertMathlibSelfAdjointOperator_central_supply_from_generator_lift I TR
      hBridge glift
  exact r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative I TR M

/-- Build full-domain continuous-representative data from generator-carrier coverage. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_generator_carrier
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorDataWithFullDomainContinuousRepresentative I TR := by
  letI : R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR :=
    r4HilbertMathlibSelfAdjointOperator_central_supply_from_generator_carrier I TR
      hBridge gcover
  exact r4HilbertMathlibSelfAdjointOperator_enrich_with_full_domain_continuous_representative I TR M

/-- Generator-carrier coverage directly closes the full bounded actual package after
constructing full-domain continuous operator data. -/
theorem r4HilbertMathlibSelfAdjointOperator_generator_carrier_to_full_domain_continuous_bounded_actual_package
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M)
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
      B.toPMap ⊤ = M.mathlibOperator ∧
        B.adjoint.toPMap ⊤ = M.mathlibOperator ∧
        B.toPMap ⊤ = B.adjoint.toPMap ⊤ ∧
        B.adjoint.toPMap ⊤ = B.toPMap ⊤ ∧
        B.adjoint = B ∧
        (B.toPMap ⊤).domain = ⊤ ∧
        (B.adjoint.toPMap ⊤).domain = ⊤ ∧
        M.mathlibOperator.domain = ⊤ ∧
        Dense (M.mathlibOperator.domain : Set
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)) ∧
        M.mathlibOperator.IsClosed ∧
        LinearPMap.adjoint M.mathlibOperator = M.mathlibOperator ∧
        M.mathlibOperator = LinearPMap.adjoint M.mathlibOperator ∧
        (LinearPMap.adjoint M.mathlibOperator).domain = M.mathlibOperator.domain ∧
        (LinearPMap.adjoint M.mathlibOperator).graph = M.mathlibOperator.graph ∧
        M.mathlibOperator.graph = M.mathlibOperator.graph.adjoint ∧
        M.mathlibOperator.graph.adjoint.toLinearPMap = M.mathlibOperator ∧
        M.mathlibOperator.IsFormalAdjoint M.mathlibOperator ∧
        M.mathlibOperator ≤ LinearPMap.adjoint M.mathlibOperator ∧
        LinearPMap.adjoint M.mathlibOperator ≤ M.mathlibOperator ∧
        (B.toPMap ⊤).graph = M.mathlibOperator.graph ∧
        (B.adjoint.toPMap ⊤).graph = M.mathlibOperator.graph ∧
        M.mathlibOperator.graph = (B.toPMap ⊤).graph ∧
        M.mathlibOperator.graph = (B.adjoint.toPMap ⊤).graph ∧
        (∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
          x ∈ M.mathlibOperator.domain) ∧
        (∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
            (hx : x ∈ M.mathlibOperator.domain),
          M.mathlibOperator ⟨x, hx⟩ = B x) ∧
        (∀ (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
            (hx : x ∈ M.mathlibOperator.domain),
          inner ℝ (M.mathlibOperator ⟨x, hx⟩) y = inner ℝ x (B y)) ∧
        (∀ x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
          inner ℝ (B x) y = inner ℝ x (B y))) := by
  let FD :=
    r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_operator_data_from_generator_carrier
      I TR hBridge gcover M
  exact r4HilbertMathlibSelfAdjointOperator_full_domain_continuous_bounded_actual_package I TR FD

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
