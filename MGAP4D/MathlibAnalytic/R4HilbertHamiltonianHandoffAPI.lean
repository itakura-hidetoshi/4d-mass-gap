import MGAP4D.MathlibAnalytic.R4HilbertHamiltonianTheoremAPI
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

/-- Handoff API for downstream self-adjointness input layers.

This API exposes the Hamiltonian carrier, domain, domain-to-generator map,
action, upstream generator handoff, and Hamiltonian input obligations. It still
does not assert self-adjointness, does not invoke a spectral theorem, and does
not state a spectral-gap result. -/
def r4HilbertHamiltonianHandoffGeneratorData
    (M : R4HilbertHamiltonianInputData I TR) :
    R4HilbertOSGeneratorInputData I TR :=
  r4HilbertHamiltonianTheoremGeneratorData I TR M

def r4HilbertHamiltonianHandoffCarrier
    (M : R4HilbertHamiltonianInputData I TR) : Type :=
  r4HilbertHamiltonianTheoremCarrier I TR M

def r4HilbertHamiltonianHandoffDomain
    (M : R4HilbertHamiltonianInputData I TR) : Type :=
  r4HilbertHamiltonianTheoremDomain I TR M

def r4HilbertHamiltonianHandoffDomainToGenerator
    (M : R4HilbertHamiltonianInputData I TR) :
    r4HilbertHamiltonianHandoffDomain I TR M →
      r4HilbertOSGeneratorHandoffDomain I TR M.generatorData :=
  r4HilbertHamiltonianTheoremDomainToGenerator I TR M

def r4HilbertHamiltonianHandoffAction
    (M : R4HilbertHamiltonianInputData I TR) :
    r4HilbertHamiltonianHandoffDomain I TR M →
      r4HilbertHamiltonianHandoffCarrier I TR M :=
  r4HilbertHamiltonianTheoremAction I TR M

theorem r4HilbertHamiltonianHandoff_generator_handoff
    (M : R4HilbertHamiltonianInputData I TR) :
    M.generatorData.semigroupData.osSemigroupReady ∧
      M.generatorData.generatorDomainDense ∧ M.generatorData.generatorGraphClosed ∧
        M.generatorData.generatorCompatibleWithSemigroup ∧
          M.generatorData.generatorDissipativeEstimate ∧ M.generatorData.generatorInputReady :=
  r4HilbertHamiltonianTheorem_generator_handoff I TR M

theorem r4HilbertHamiltonianHandoff_compatible_with_generator
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianCompatibleWithGenerator :=
  r4HilbertHamiltonianTheorem_compatible_with_generator I TR M

theorem r4HilbertHamiltonianHandoff_nonnegative_form
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianNonnegativeFormInput :=
  r4HilbertHamiltonianTheorem_nonnegative_form I TR M

theorem r4HilbertHamiltonianHandoff_symmetric_on_domain
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianSymmetricOnDomainInput :=
  r4HilbertHamiltonianTheorem_symmetric_on_domain I TR M

theorem r4HilbertHamiltonianHandoff_closability
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianClosabilityInput :=
  r4HilbertHamiltonianTheorem_closability I TR M

theorem r4HilbertHamiltonianHandoff_ready
    (M : R4HilbertHamiltonianInputData I TR) :
    M.hamiltonianInputReady :=
  r4HilbertHamiltonianTheorem_ready I TR M

theorem r4HilbertHamiltonianHandoff_bundle
    (M : R4HilbertHamiltonianInputData I TR) :
    (M.generatorData.semigroupData.osSemigroupReady ∧
      M.generatorData.generatorDomainDense ∧ M.generatorData.generatorGraphClosed ∧
        M.generatorData.generatorCompatibleWithSemigroup ∧
          M.generatorData.generatorDissipativeEstimate ∧ M.generatorData.generatorInputReady) ∧
      (M.hamiltonianCompatibleWithGenerator ∧ M.hamiltonianNonnegativeFormInput ∧
        M.hamiltonianSymmetricOnDomainInput ∧ M.hamiltonianClosabilityInput ∧
          M.hamiltonianInputReady) :=
  r4HilbertHamiltonianTheorem_constructed I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
