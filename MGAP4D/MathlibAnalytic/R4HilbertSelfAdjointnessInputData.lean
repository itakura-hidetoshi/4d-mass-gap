import MGAP4D.MathlibAnalytic.R4HilbertHamiltonianHandoffAPI
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

/-- Input data for a self-adjointness criterion for the R4 Hamiltonian handoff.

This layer records the additional graph/core and adjoint-domain obligations that
would be needed before a self-adjoint Hamiltonian theorem. It does not assert
self-adjointness, does not invoke a spectral theorem, and does not state a
spectral-gap result. -/
structure R4HilbertSelfAdjointnessInputData where
  hamiltonianData : R4HilbertHamiltonianInputData I TR
  operatorCore : Type
  operatorCoreToHamiltonianDomain :
    operatorCore → r4HilbertHamiltonianHandoffDomain I TR hamiltonianData
  coreDenseForGraphInput : Prop
  coreDenseForGraphInput_holds : coreDenseForGraphInput
  adjointDomainControlledInput : Prop
  adjointDomainControlledInput_holds : adjointDomainControlledInput
  symmetricClosureInput : Prop
  symmetricClosureInput_holds : symmetricClosureInput
  deficiencyIndexVanishingInput : Prop
  deficiencyIndexVanishingInput_holds : deficiencyIndexVanishingInput
  selfAdjointnessInputReady : Prop
  selfAdjointnessInputReady_holds : selfAdjointnessInputReady

def r4HilbertSelfAdjointnessInputHamiltonianData
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    R4HilbertHamiltonianInputData I TR :=
  M.hamiltonianData

def r4HilbertSelfAdjointnessInputCarrier
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  r4HilbertHamiltonianHandoffCarrier I TR M.hamiltonianData

def r4HilbertSelfAdjointnessInputHamiltonianDomain
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  r4HilbertHamiltonianHandoffDomain I TR M.hamiltonianData

def r4HilbertSelfAdjointnessInputCore
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  M.operatorCore

def r4HilbertSelfAdjointnessInputCoreMap
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    r4HilbertSelfAdjointnessInputCore I TR M →
      r4HilbertSelfAdjointnessInputHamiltonianDomain I TR M :=
  M.operatorCoreToHamiltonianDomain

def r4HilbertSelfAdjointnessInputHamiltonianAction
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    r4HilbertSelfAdjointnessInputHamiltonianDomain I TR M →
      r4HilbertSelfAdjointnessInputCarrier I TR M :=
  r4HilbertHamiltonianHandoffAction I TR M.hamiltonianData

theorem r4HilbertSelfAdjointnessInput_hamiltonian_handoff
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
  r4HilbertHamiltonianHandoff_bundle I TR M.hamiltonianData

theorem r4HilbertSelfAdjointnessInput_core_dense
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.coreDenseForGraphInput :=
  M.coreDenseForGraphInput_holds

theorem r4HilbertSelfAdjointnessInput_adjoint_domain_controlled
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.adjointDomainControlledInput :=
  M.adjointDomainControlledInput_holds

theorem r4HilbertSelfAdjointnessInput_symmetric_closure
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.symmetricClosureInput :=
  M.symmetricClosureInput_holds

theorem r4HilbertSelfAdjointnessInput_deficiency_index_vanishing
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.deficiencyIndexVanishingInput :=
  M.deficiencyIndexVanishingInput_holds

theorem r4HilbertSelfAdjointnessInput_ready
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.selfAdjointnessInputReady :=
  M.selfAdjointnessInputReady_holds

theorem r4HilbertSelfAdjointnessInput_bundle
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    M.coreDenseForGraphInput ∧ M.adjointDomainControlledInput ∧
      M.symmetricClosureInput ∧ M.deficiencyIndexVanishingInput ∧
        M.selfAdjointnessInputReady :=
  ⟨r4HilbertSelfAdjointnessInput_core_dense I TR M,
    r4HilbertSelfAdjointnessInput_adjoint_domain_controlled I TR M,
    r4HilbertSelfAdjointnessInput_symmetric_closure I TR M,
    r4HilbertSelfAdjointnessInput_deficiency_index_vanishing I TR M,
    r4HilbertSelfAdjointnessInput_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
