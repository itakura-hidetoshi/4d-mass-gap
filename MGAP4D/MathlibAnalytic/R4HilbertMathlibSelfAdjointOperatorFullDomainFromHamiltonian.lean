import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorFullDomainData
import MGAP4D.MathlibAnalytic.R4HilbertHamiltonianInputData
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

/-! Full-domain route from the OS-generator/Hamiltonian construction layer. -/

/-- Hamiltonian-side full-domain transfer data for the actual R4 mathlib operator.

The existing OS-generator and Hamiltonian input structures carry generator domains,
Hamiltonian domains, closedness, symmetry, nonnegativity, closability, and readiness.
They do not by themselves contain a theorem that the final mathlib `LinearPMap`
has top domain. This data records precisely the remaining construction theorem:
the Hamiltonian construction transfers total-domain coverage to the actual
mathlib operator. -/
structure R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  hamiltonianInput : R4HilbertHamiltonianInputData I TR
  hamiltonianInputReady : hamiltonianInput.hamiltonianInputReady
  compatibleWithActualOperator : M.mathlibOperatorCompatibleWithHamiltonianInput
  totalDomainTransferredToActual :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    M.mathlibOperator.domain = ⊤)

/-- Extract the Hamiltonian input carried by the full-domain transfer datum. -/
def r4HilbertMathlibSelfAdjointOperator_hamiltonian_full_domain_input
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HD : R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData I TR M) :
    R4HilbertHamiltonianInputData I TR :=
  HD.hamiltonianInput

/-- The Hamiltonian-side transfer datum gives the actual operator full-domain theorem. -/
theorem r4HilbertMathlibSelfAdjointOperator_domain_eq_top_from_hamiltonian_full_domain
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HD : R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    M.mathlibOperator.domain = ⊤) :=
  HD.totalDomainTransferredToActual

/-- The Hamiltonian-side full-domain transfer datum constructs the `FullDomainData`
needed by the bounded route. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HD : R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  { domain_eq_top :=
      r4HilbertMathlibSelfAdjointOperator_domain_eq_top_from_hamiltonian_full_domain I TR HD }

/-- Package theorem: Hamiltonian construction transfer gives the full-domain datum,
the domain equality, Hamiltonian compatibility, and Hamiltonian readiness together. -/
theorem r4HilbertMathlibSelfAdjointOperator_hamiltonian_full_domain_package
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (HD : R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M ∧
      (letI : NormedAddCommGroup
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
      letI : InnerProductSpace ℝ
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
        r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
      M.mathlibOperator.domain = ⊤) ∧
        M.mathlibOperatorCompatibleWithHamiltonianInput ∧
          HD.hamiltonianInput.hamiltonianInputReady := by
  exact ⟨
    r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian I TR HD,
    r4HilbertMathlibSelfAdjointOperator_domain_eq_top_from_hamiltonian_full_domain I TR HD,
    HD.compatibleWithActualOperator,
    HD.hamiltonianInputReady⟩

/-- A family-level Hamiltonian full-domain transfer gives the family-level
full-domain data required by the bounded route family. -/
def r4HilbertMathlibSelfAdjointOperator_full_domain_family_from_hamiltonian
    (HD : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianFullDomainData I TR M) :
    ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorFullDomainData I TR M :=
  fun M => r4HilbertMathlibSelfAdjointOperator_full_domain_data_from_hamiltonian I TR (HD M)

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
