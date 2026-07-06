import MGAP4D.MathlibAnalytic.R4HilbertOSGeneratorInputData
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

def r4HilbertOSGeneratorTheoremSemigroupData
    (M : R4HilbertOSGeneratorInputData I TR) :
    R4HilbertCompletedOSSemigroupInputData I TR :=
  r4HilbertOSGeneratorInputSemigroupData I TR M

def r4HilbertOSGeneratorTheoremCarrier
    (M : R4HilbertOSGeneratorInputData I TR) : Type :=
  r4HilbertOSGeneratorInputCarrier I TR M

def r4HilbertOSGeneratorTheoremDomain
    (M : R4HilbertOSGeneratorInputData I TR) : Type :=
  r4HilbertOSGeneratorInputDomain I TR M

def r4HilbertOSGeneratorTheoremDomainMap
    (M : R4HilbertOSGeneratorInputData I TR) :
    r4HilbertOSGeneratorTheoremDomain I TR M → r4HilbertOSGeneratorTheoremCarrier I TR M :=
  r4HilbertOSGeneratorInputDomainMap I TR M

def r4HilbertOSGeneratorTheoremAction
    (M : R4HilbertOSGeneratorInputData I TR) :
    r4HilbertOSGeneratorTheoremDomain I TR M → r4HilbertOSGeneratorTheoremCarrier I TR M :=
  r4HilbertOSGeneratorInputAction I TR M

theorem r4HilbertOSGeneratorTheorem_domain_dense
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDomainDense :=
  r4HilbertOSGeneratorInput_domain_dense I TR M

theorem r4HilbertOSGeneratorTheorem_graph_closed
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorGraphClosed :=
  r4HilbertOSGeneratorInput_graph_closed I TR M

theorem r4HilbertOSGeneratorTheorem_compatible_with_semigroup
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorCompatibleWithSemigroup :=
  r4HilbertOSGeneratorInput_compatible_with_semigroup I TR M

theorem r4HilbertOSGeneratorTheorem_dissipative_estimate
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDissipativeEstimate :=
  r4HilbertOSGeneratorInput_dissipative_estimate I TR M

theorem r4HilbertOSGeneratorTheorem_ready
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorInputReady :=
  r4HilbertOSGeneratorInput_ready I TR M

theorem r4HilbertOSGeneratorTheorem_bundle
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDomainDense ∧ M.generatorGraphClosed ∧
      M.generatorCompatibleWithSemigroup ∧ M.generatorDissipativeEstimate ∧
        M.generatorInputReady :=
  r4HilbertOSGeneratorInput_bundle I TR M

/-- The theorem API for OS generator input data.

This packages the generator-domain and graph obligations without identifying
the generator as a physical Hamiltonian and without asserting self-adjointness
or a spectral-gap theorem. -/
theorem r4HilbertOSGeneratorTheorem_constructed
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDomainDense ∧ M.generatorGraphClosed ∧
      M.generatorCompatibleWithSemigroup ∧ M.generatorDissipativeEstimate ∧
        M.generatorInputReady :=
  r4HilbertOSGeneratorTheorem_bundle I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
