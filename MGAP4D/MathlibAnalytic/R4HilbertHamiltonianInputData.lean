import MGAP4D.MathlibAnalytic.R4HilbertOSGeneratorHandoffAPI
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

/-- Input data for a candidate Hamiltonian associated with the R4 OS generator.

This layer records a Hamiltonian-domain graph and its compatibility with the OS
generator handoff. It does not assert self-adjointness, does not invoke a
spectral theorem, and does not state a spectral-gap result. -/
structure R4HilbertHamiltonianInputData where
  generatorData : R4HilbertOSGeneratorInputData I TR
  hamiltonianDomain : Type
  hamiltonianDomainToGeneratorDomain :
    hamiltonianDomain → r4HilbertOSGeneratorHandoffDomain I TR generatorData
  hamiltonianAction :
    hamiltonianDomain → r4HilbertOSGeneratorHandoffCarrier I TR generatorData
  hamiltonianCompatibleWithGenerator : Prop
  hamiltonianCompatibleWithGenerator_holds : hamiltonianCompatibleWithGenerator
  hamiltonianNonnegativeFormInput : Prop
  hamiltonianNonnegativeFormInput_holds : hamiltonianNonnegativeFormInput
  hamiltonianSymmetricOnDomainInput : Prop
  hamiltonianSymmetricOnDomainInput_holds : hamiltonianSymmetricOnDomainInput
  hamiltonianClosabilityInput : Prop
  hamiltonianClosabilityInput_holds : hamiltonianClosabilityInput
  hamiltonianInputReady : Prop
  hamiltonianInputReady_holds : hamiltonianInputReady

def r4HilbertHamiltonianInputGeneratorData
    (M : R4HilbertHamiltonianInputData I TR) :
    R4HilbertOSGeneratorInputData I TR :=
  M.generatorData

def r4HilbertHamiltonianInputCarrier
    (M : R4HilbertHamiltonianInputData I TR) : Type :=
  r4HilbertOSGeneratorHandoffCarrier I TR M.generatorData

def r4HilbertHamiltonianInputDomain
    (M : R4HilbertHamiltonianInputData I TR) : Type :=
  M.hamiltonianDomain

def r4HilbertHamiltonianInputDomainToGenerator
    (M : R4HilbertHamiltonianInputData I TR) :
    r4HilbertHamiltonianInputDomain I TR M →
      r4HilbertOSGeneratorHandoffDomain I TR M.generatorData :=
  M.hamiltonianDomainToGeneratorDomain

def r4HilbertHamiltonianInputAction
    (M : R4HilbertHamiltonianInputData I TR) :
    r4HilbertHamiltonianInputDomain I TR M → r4HilbertHamiltonianInputCarrier I TR M :=
  M.hamiltonianAction

theorem r4HilbertHamiltonianInput_generator_handoff
    (M : R4HilbertHamiltonianInputData I TR) :
    M.generatorData.semigroupData.osSemigroupReady ∧
      M.generatorData.generatorDomainDense ∧ M.generatorData.generatorGraphClosed ∧
        M.generatorData.generatorCompatibleWithSemigroup ∧
          M.generatorData.generatorDissipativeEstimate ∧ M.generatorData.generatorInputReady :=
  r4HilbertOSGeneratorHandoff_bundle I TR M.generatorData

theorem r4HilbertHamiltonianInput_compatible_with_generator
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianCompatibleWithGenerator :=
  M.hamiltonianCompatibleWithGenerator_holds

theorem r4HilbertHamiltonianInput_nonnegative_form
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianNonnegativeFormInput :=
  M.hamiltonianNonnegativeFormInput_holds

theorem r4HilbertHamiltonianInput_symmetric_on_domain
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianSymmetricOnDomainInput :=
  M.hamiltonianSymmetricOnDomainInput_holds

theorem r4HilbertHamiltonianInput_closability
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianClosabilityInput :=
  M.hamiltonianClosabilityInput_holds

theorem r4HilbertHamiltonianInput_ready
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianInputReady :=
  M.hamiltonianInputReady_holds

theorem r4HilbertHamiltonianInput_bundle
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianCompatibleWithGenerator ∧ M.hamiltonianNonnegativeFormInput ∧
      M.hamiltonianSymmetricOnDomainInput ∧ M.hamiltonianClosabilityInput ∧
        M.hamiltonianInputReady :=
  ⟨r4HilbertHamiltonianInput_compatible_with_generator I TR M,
    r4HilbertHamiltonianInput_nonnegative_form I TR M,
    r4HilbertHamiltonianInput_symmetric_on_domain I TR M,
    r4HilbertHamiltonianInput_closability I TR M,
    r4HilbertHamiltonianInput_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
