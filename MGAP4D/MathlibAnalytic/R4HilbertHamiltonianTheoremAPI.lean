import MGAP4D.MathlibAnalytic.R4HilbertHamiltonianInputData
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

def r4HilbertHamiltonianTheoremGeneratorData
    (M : R4HilbertHamiltonianInputData I TR) :
    R4HilbertOSGeneratorInputData I TR :=
  r4HilbertHamiltonianInputGeneratorData I TR M

def r4HilbertHamiltonianTheoremCarrier
    (M : R4HilbertHamiltonianInputData I TR) : Type :=
  r4HilbertHamiltonianInputCarrier I TR M

def r4HilbertHamiltonianTheoremDomain
    (M : R4HilbertHamiltonianInputData I TR) : Type :=
  r4HilbertHamiltonianInputDomain I TR M

def r4HilbertHamiltonianTheoremDomainToGenerator
    (M : R4HilbertHamiltonianInputData I TR) :
    r4HilbertHamiltonianTheoremDomain I TR M →
      r4HilbertOSGeneratorHandoffDomain I TR M.generatorData :=
  r4HilbertHamiltonianInputDomainToGenerator I TR M

def r4HilbertHamiltonianTheoremAction
    (M : R4HilbertHamiltonianInputData I TR) :
    r4HilbertHamiltonianTheoremDomain I TR M →
      r4HilbertHamiltonianTheoremCarrier I TR M :=
  r4HilbertHamiltonianInputAction I TR M

theorem r4HilbertHamiltonianTheorem_generator_handoff
    (M : R4HilbertHamiltonianInputData I TR) :
    M.generatorData.semigroupData.osSemigroupReady ∧
      M.generatorData.generatorDomainDense ∧ M.generatorData.generatorGraphClosed ∧
        M.generatorData.generatorCompatibleWithSemigroup ∧
          M.generatorData.generatorDissipativeEstimate ∧ M.generatorData.generatorInputReady :=
  r4HilbertHamiltonianInput_generator_handoff I TR M

theorem r4HilbertHamiltonianTheorem_compatible_with_generator
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianCompatibleWithGenerator :=
  r4HilbertHamiltonianInput_compatible_with_generator I TR M

theorem r4HilbertHamiltonianTheorem_nonnegative_form
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianNonnegativeFormInput :=
  r4HilbertHamiltonianInput_nonnegative_form I TR M

theorem r4HilbertHamiltonianTheorem_symmetric_on_domain
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianSymmetricOnDomainInput :=
  r4HilbertHamiltonianInput_symmetric_on_domain I TR M

theorem r4HilbertHamiltonianTheorem_closability
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianClosabilityInput :=
  r4HilbertHamiltonianInput_closability I TR M

theorem r4HilbertHamiltonianTheorem_ready
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianInputReady :=
  r4HilbertHamiltonianInput_ready I TR M

theorem r4HilbertHamiltonianTheorem_bundle
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianCompatibleWithGenerator ∧ M.hamiltonianNonnegativeFormInput ∧
      M.hamiltonianSymmetricOnDomainInput ∧ M.hamiltonianClosabilityInput ∧
        M.hamiltonianInputReady :=
  r4HilbertHamiltonianInput_bundle I TR M

/-- The theorem API for the R4 Hamiltonian input layer.

This theorem combines the upstream OS-generator handoff readiness with the
Hamiltonian input obligations. It still does not assert self-adjointness, does
not invoke a spectral theorem, and does not state a spectral-gap result. -/
theorem r4HilbertHamiltonianTheorem_constructed
    (M : R4HilbertHamiltonianInputData I TR) :
    (M.generatorData.semigroupData.osSemigroupReady ∧
      M.generatorData.generatorDomainDense ∧ M.generatorData.generatorGraphClosed ∧
        M.generatorData.generatorCompatibleWithSemigroup ∧
          M.generatorData.generatorDissipativeEstimate ∧ M.generatorData.generatorInputReady) ∧
      (M.hamiltonianCompatibleWithGenerator ∧ M.hamiltonianNonnegativeFormInput ∧
        M.hamiltonianSymmetricOnDomainInput ∧ M.hamiltonianClosabilityInput ∧
          M.hamiltonianInputReady) :=
  ⟨r4HilbertHamiltonianTheorem_generator_handoff I TR M,
    r4HilbertHamiltonianTheorem_bundle I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
