import MGAP4D.MathlibAnalytic.R4HilbertSelfAdjointnessTheoremAPI
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

/-- Handoff API for downstream spectral-theorem input layers.

This API exposes the self-adjointness criterion input data, including the
Hamiltonian carrier, domain, core, core map, action, upstream Hamiltonian handoff,
and readiness obligations. It still does not assert self-adjointness, does not
invoke a spectral theorem, and does not state a spectral-gap result. -/
def r4HilbertSelfAdjointnessHandoffHamiltonianData
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    R4HilbertHamiltonianInputData I TR :=
  r4HilbertSelfAdjointnessTheoremHamiltonianData I TR M

def r4HilbertSelfAdjointnessHandoffCarrier
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  r4HilbertSelfAdjointnessTheoremCarrier I TR M

def r4HilbertSelfAdjointnessHandoffHamiltonianDomain
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  r4HilbertSelfAdjointnessTheoremHamiltonianDomain I TR M

def r4HilbertSelfAdjointnessHandoffCore
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  r4HilbertSelfAdjointnessTheoremCore I TR M

def r4HilbertSelfAdjointnessHandoffCoreMap
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    r4HilbertSelfAdjointnessHandoffCore I TR M →
      r4HilbertSelfAdjointnessHandoffHamiltonianDomain I TR M :=
  r4HilbertSelfAdjointnessTheoremCoreMap I TR M

def r4HilbertSelfAdjointnessHandoffHamiltonianAction
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    r4HilbertSelfAdjointnessHandoffHamiltonianDomain I TR M →
      r4HilbertSelfAdjointnessHandoffCarrier I TR M :=
  r4HilbertSelfAdjointnessTheoremHamiltonianAction I TR M

theorem r4HilbertSelfAdjointnessHandoff_hamiltonian_handoff
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
  r4HilbertSelfAdjointnessTheorem_hamiltonian_handoff I TR M

theorem r4HilbertSelfAdjointnessHandoff_core_dense
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.coreDenseForGraphInput :=
  r4HilbertSelfAdjointnessTheorem_core_dense I TR M

theorem r4HilbertSelfAdjointnessHandoff_adjoint_domain_controlled
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.adjointDomainControlledInput :=
  r4HilbertSelfAdjointnessTheorem_adjoint_domain_controlled I TR M

theorem r4HilbertSelfAdjointnessHandoff_symmetric_closure
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.symmetricClosureInput :=
  r4HilbertSelfAdjointnessTheorem_symmetric_closure I TR M

theorem r4HilbertSelfAdjointnessHandoff_deficiency_index_vanishing
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.deficiencyIndexVanishingInput :=
  r4HilbertSelfAdjointnessTheorem_deficiency_index_vanishing I TR M

theorem r4HilbertSelfAdjointnessHandoff_ready
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.selfAdjointnessInputReady :=
  r4HilbertSelfAdjointnessTheorem_ready I TR M

theorem r4HilbertSelfAdjointnessHandoff_bundle
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
      (M.coreDenseForGraphInput ∧ M.adjointDomainControlledInput ∧
        M.symmetricClosureInput ∧ M.deficiencyIndexVanishingInput ∧
          M.selfAdjointnessInputReady) :=
  r4HilbertSelfAdjointnessTheorem_constructed I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
