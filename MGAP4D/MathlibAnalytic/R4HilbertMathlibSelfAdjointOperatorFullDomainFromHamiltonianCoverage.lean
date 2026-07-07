import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainFromHamiltonian
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

/-! Full-domain proof from pointwise Hamiltonian coverage. -/

/-- Hamiltonian-side pointwise coverage of the actual R4 mathlib operator domain.

This is the next internalization step after the direct full-domain transfer datum:
instead of storing `M.mathlibOperator.domain = ⊤` directly, it stores that every
carrier vector is covered by the actual operator domain. The equality with `⊤`
is then proved below by submodule order. -/
structure R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  hamiltonianInput : R4HilbertHamiltonianInputData I TR
  hamiltonianInputReady : hamiltonianInput.hamiltonianInputReady
  compatibleWithActualOperator : M.mathlibOperatorCompatibleWithHamiltonianInput
  actualDomainCoversCarrier :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
      x ∈ M.mathlibOperator.domain)

/-- Pointwise Hamiltonian coverage proves that the actual operator domain is top. -/
theorem r4HilbertMathlibSelfAdjointOperator_domain_eq_top_from_hamiltonian_coverage
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HC : R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    M.mathlibOperator.domain = ⊤) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  apply le_antisymm
  · exact le_top
  · intro x _hx
    exact HC.actualDomainCoversCarrier x

/-- Pointwise Hamiltonian coverage constructs the direct Hamiltonian full-domain
transfer datum from the previous layer. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_full_domain_from_coverage
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HC : R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData I TR M :=
  { hamiltonianInput := HC.hamiltonianInput
    hamiltonianInputReady := HC.hamiltonianInputReady
    compatibleWithActualOperator := HC.compatibleWithActualOperator
    totalDomainTransferredToActual :=
      r4HilbertMathlibSelfAdjointOperator_domain_eq_top_from_hamiltonian_coverage I TR HC }

/-- Pointwise Hamiltonian coverage constructs the `FullDomainData` required by the
bounded route. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_coverage
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HC : R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian I TR
    (r4HilbertMathlibSelfAdjointOperator_hamiltonian_full_domain_from_coverage I TR HC)

/-- Package theorem: pointwise Hamiltonian coverage gives the full-domain datum,
the domain equality, the pointwise coverage theorem, Hamiltonian compatibility,
and Hamiltonian readiness together. -/
theorem r4HilbertMathlibSelfAdjointOperator_hamiltonian_coverage_full_domain_package
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HC : R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) ∧
        (letI : NormedAddCommGroup
            (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
          r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
        letI : InnerProductSpace ℝ
            (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
          r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
        ∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
          x ∈ M.mathlibOperator.domain) ∧
          M.mathlibOperatorCompatibleWithHamiltonianInput ∧
            HC.hamiltonianInput.hamiltonianInputReady := by
  exact ⟨
    r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian_coverage I TR HC,
    r4HilbertMathlibSelfAdjointOperator_domain_eq_top_from_hamiltonian_coverage I TR HC,
    HC.actualDomainCoversCarrier,
    HC.compatibleWithActualOperator,
    HC.hamiltonianInputReady⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
