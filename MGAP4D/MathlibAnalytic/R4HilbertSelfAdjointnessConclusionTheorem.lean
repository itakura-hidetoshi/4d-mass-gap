import MGAP4D.MathlibAnalytic.R4HilbertSelfAdjointnessHandoffAPI
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

/-- The criterion-level self-adjointness conclusion for the R4 Hamiltonian input.

This is the first conclusion theorem layer for self-adjointness. It concludes the
abstract self-adjointness criterion from the already supplied core-density,
adjoint-domain control, symmetric-closure, deficiency-index vanishing, and
readiness obligations. It does not build a mathlib unbounded self-adjoint
operator object, does not invoke a spectral theorem, and does not state a
spectral-gap result. -/
def r4HilbertSelfAdjointnessConclusion
    (M : R4HilbertSelfAdjointnessInputData I TR) : Prop :=
  M.coreDenseForGraphInput ∧ M.adjointDomainControlledInput ∧
    M.symmetricClosureInput ∧ M.deficiencyIndexVanishingInput ∧
      M.selfAdjointnessInputReady

theorem r4HilbertSelfAdjointnessConclusion_hamiltonian_handoff
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    (M.hamiltonianData.generatorData.semigroupData.osSemigroupReady ∧
      M.hamiltonianData.generatorData.generatorDomainDense ∧
        M.hamiltonianData.generatorData.generatorGraphClosed ∧
          M.hamiltonianData.generatorData.generatorCompatibleWithSemigroup ∧
            M.hamiltonianData.generatorData.generatorDissipativeEstimate ∧
              M.hamiltonianData.generatorData.generatorInputReady) ∧
      (M.hamiltonianData.hamiltonianCompatibleWithGenerator ∧
        M.hamiltonianData.hamiltonianNonnegativeFormInput ∧
          M.hamiltonianData.hamiltonianSymmetricOnDomainInput ∧
            M.hamiltonianData.hamiltonianClosabilityInput ∧
              M.hamiltonianData.hamiltonianInputReady) :=
  r4HilbertSelfAdjointnessHandoff_hamiltonian_handoff I TR M

theorem r4HilbertSelfAdjointnessConclusion_core_dense
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.coreDenseForGraphInput :=
  r4HilbertSelfAdjointnessHandoff_core_dense I TR M

theorem r4HilbertSelfAdjointnessConclusion_adjoint_domain_controlled
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.adjointDomainControlledInput :=
  r4HilbertSelfAdjointnessHandoff_adjoint_domain_controlled I TR M

theorem r4HilbertSelfAdjointnessConclusion_symmetric_closure
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.symmetricClosureInput :=
  r4HilbertSelfAdjointnessHandoff_symmetric_closure I TR M

theorem r4HilbertSelfAdjointnessConclusion_deficiency_index_vanishing
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.deficiencyIndexVanishingInput :=
  r4HilbertSelfAdjointnessHandoff_deficiency_index_vanishing I TR M

/-- Direct conclusion of the abstract self-adjointness criterion. -/
theorem r4HilbertSelfAdjointnessConclusion_self_adjoint
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.selfAdjointnessInputReady :=
  r4HilbertSelfAdjointnessHandoff_ready I TR M

/-- The self-adjointness conclusion theorem.

The theorem closes the criterion-level self-adjointness conclusion from the
existing input obligations. It is deliberately separated from the spectral
Theorem and spectral-gap layers. -/
theorem r4HilbertSelfAdjointnessConclusion_proved
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    r4HilbertSelfAdjointnessConclusion I TR M :=
  ⟨r4HilbertSelfAdjointnessConclusion_core_dense I TR M,
    r4HilbertSelfAdjointnessConclusion_adjoint_domain_controlled I TR M,
    r4HilbertSelfAdjointnessConclusion_symmetric_closure I TR M,
    r4HilbertSelfAdjointnessConclusion_deficiency_index_vanishing I TR M,
    r4HilbertSelfAdjointnessConclusion_self_adjoint I TR M⟩

/-- Combined upstream Hamiltonian handoff plus the self-adjointness conclusion. -/
theorem r4HilbertSelfAdjointnessTheorem_proved
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    ((M.hamiltonianData.generatorData.semigroupData.osSemigroupReady ∧
      M.hamiltonianData.generatorData.generatorDomainDense ∧
        M.hamiltonianData.generatorData.generatorGraphClosed ∧
          M.hamiltonianData.generatorData.generatorCompatibleWithSemigroup ∧
            M.hamiltonianData.generatorData.generatorDissipativeEstimate ∧
              M.hamiltonianData.generatorData.generatorInputReady) ∧
      (M.hamiltonianData.hamiltonianCompatibleWithGenerator ∧
        M.hamiltonianData.hamiltonianNonnegativeFormInput ∧
          M.hamiltonianData.hamiltonianSymmetricOnDomainInput ∧
            M.hamiltonianData.hamiltonianClosabilityInput ∧
              M.hamiltonianData.hamiltonianInputReady)) ∧
      r4HilbertSelfAdjointnessConclusion I TR M :=
  ⟨r4HilbertSelfAdjointnessConclusion_hamiltonian_handoff I TR M,
    r4HilbertSelfAdjointnessConclusion_proved I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
