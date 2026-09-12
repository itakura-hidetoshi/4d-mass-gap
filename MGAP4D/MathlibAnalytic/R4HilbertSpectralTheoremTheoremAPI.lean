import MGAP4D.MathlibAnalytic.R4HilbertSpectralTheoremInputData
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

def r4HilbertSpectralTheoremTheoremSelfAdjointnessData
    (M : R4HilbertSpectralTheoremInputData I TR) :
    R4HilbertSelfAdjointnessInputData I TR :=
  r4HilbertSpectralTheoremInputSelfAdjointnessData I TR M

def r4HilbertSpectralTheoremTheoremCarrier
    (M : R4HilbertSpectralTheoremInputData I TR) : Type :=
  r4HilbertSpectralTheoremInputCarrier I TR M

def r4HilbertSpectralTheoremTheoremHamiltonianDomain
    (M : R4HilbertSpectralTheoremInputData I TR) : Type :=
  r4HilbertSpectralTheoremInputHamiltonianDomain I TR M

def r4HilbertSpectralTheoremTheoremHamiltonianAction
    (M : R4HilbertSpectralTheoremInputData I TR) :
    r4HilbertSpectralTheoremTheoremHamiltonianDomain I TR M →
      r4HilbertSpectralTheoremTheoremCarrier I TR M :=
  r4HilbertSpectralTheoremInputHamiltonianAction I TR M

def r4HilbertSpectralTheoremTheoremParameter
    (M : R4HilbertSpectralTheoremInputData I TR) : Type :=
  r4HilbertSpectralTheoremInputParameter I TR M

def r4HilbertSpectralTheoremTheoremProjectionFamily
    (M : R4HilbertSpectralTheoremInputData I TR) :
    r4HilbertSpectralTheoremTheoremParameter I TR M → Prop :=
  r4HilbertSpectralTheoremInputProjectionFamily I TR M

theorem r4HilbertSpectralTheoremTheorem_self_adjointness_handoff
    (M : R4HilbertSpectralTheoremInputData I TR) :
    ((M.selfAdjointnessData.hamiltonianData.generatorData.semigroupData.osSemigroupReady ∧
      M.selfAdjointnessData.hamiltonianData.generatorData.generatorDomainDense ∧
        M.selfAdjointnessData.hamiltonianData.generatorData.generatorGraphClosed ∧
          M.selfAdjointnessData.hamiltonianData.generatorData.generatorCompatibleWithSemigroup ∧
            M.selfAdjointnessData.hamiltonianData.generatorData.generatorDissipativeEstimate ∧
              M.selfAdjointnessData.hamiltonianData.generatorData.generatorInputReady) ∧
      (M.selfAdjointnessData.hamiltonianData.hamiltonianCompatibleWithGenerator ∧
        M.selfAdjointnessData.hamiltonianData.hamiltonianNonnegativeFormInput ∧
          M.selfAdjointnessData.hamiltonianData.hamiltonianSymmetricOnDomainInput ∧
            M.selfAdjointnessData.hamiltonianData.hamiltonianClosabilityInput ∧
              M.selfAdjointnessData.hamiltonianData.hamiltonianInputReady)) ∧
      (M.selfAdjointnessData.coreDenseForGraphInput ∧
        M.selfAdjointnessData.adjointDomainControlledInput ∧
          M.selfAdjointnessData.symmetricClosureInput ∧
            M.selfAdjointnessData.deficiencyIndexVanishingInput ∧
              M.selfAdjointnessData.selfAdjointnessInputReady) :=
  r4HilbertSpectralTheoremInput_self_adjointness_handoff I TR M

theorem r4HilbertSpectralTheoremTheorem_projection_family
    (M : R4HilbertSpectralTheoremInputData I TR)
    (a : r4HilbertSpectralTheoremTheoremParameter I TR M) :
    r4HilbertSpectralTheoremTheoremProjectionFamily I TR M a :=
  r4HilbertSpectralTheoremInput_projection_family I TR M a

theorem r4HilbertSpectralTheoremTheorem_resolution
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.spectralResolutionInput :=
  r4HilbertSpectralTheoremInput_resolution I TR M

theorem r4HilbertSpectralTheoremTheorem_functional_calculus
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.functionalCalculusInput :=
  r4HilbertSpectralTheoremInput_functional_calculus I TR M

theorem r4HilbertSpectralTheoremTheorem_measure_compatibility
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.spectralMeasureCompatibilityInput :=
  r4HilbertSpectralTheoremInput_measure_compatibility I TR M

theorem r4HilbertSpectralTheoremTheorem_self_adjoint_operator
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.selfAdjointOperatorInput :=
  r4HilbertSpectralTheoremInput_self_adjoint_operator I TR M

theorem r4HilbertSpectralTheoremTheorem_ready
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.spectralTheoremInputReady :=
  r4HilbertSpectralTheoremInput_ready I TR M

theorem r4HilbertSpectralTheoremTheorem_bundle
    (M : R4HilbertSpectralTheoremInputData I TR) :
    (∀ a : r4HilbertSpectralTheoremTheoremParameter I TR M,
      r4HilbertSpectralTheoremTheoremProjectionFamily I TR M a) ∧
      M.spectralResolutionInput ∧ M.functionalCalculusInput ∧
        M.spectralMeasureCompatibilityInput ∧ M.selfAdjointOperatorInput ∧
          M.spectralTheoremInputReady :=
  ⟨r4HilbertSpectralTheoremTheorem_projection_family I TR M,
    r4HilbertSpectralTheoremTheorem_resolution I TR M,
    r4HilbertSpectralTheoremTheorem_functional_calculus I TR M,
    r4HilbertSpectralTheoremTheorem_measure_compatibility I TR M,
    r4HilbertSpectralTheoremTheorem_self_adjoint_operator I TR M,
    r4HilbertSpectralTheoremTheorem_ready I TR M⟩

/-- The theorem API for the R4 spectral-theorem input layer.

This theorem combines the upstream self-adjointness handoff with the spectral
input obligations. It still does not prove self-adjointness, does not invoke a
spectral theorem, and does not state a spectral-gap result. -/
theorem r4HilbertSpectralTheoremTheorem_constructed
    (M : R4HilbertSpectralTheoremInputData I TR) :
    (((M.selfAdjointnessData.hamiltonianData.generatorData.semigroupData.osSemigroupReady ∧
      M.selfAdjointnessData.hamiltonianData.generatorData.generatorDomainDense ∧
        M.selfAdjointnessData.hamiltonianData.generatorData.generatorGraphClosed ∧
          M.selfAdjointnessData.hamiltonianData.generatorData.generatorCompatibleWithSemigroup ∧
            M.selfAdjointnessData.hamiltonianData.generatorData.generatorDissipativeEstimate ∧
              M.selfAdjointnessData.hamiltonianData.generatorData.generatorInputReady) ∧
      (M.selfAdjointnessData.hamiltonianData.hamiltonianCompatibleWithGenerator ∧
        M.selfAdjointnessData.hamiltonianData.hamiltonianNonnegativeFormInput ∧
          M.selfAdjointnessData.hamiltonianData.hamiltonianSymmetricOnDomainInput ∧
            M.selfAdjointnessData.hamiltonianData.hamiltonianClosabilityInput ∧
              M.selfAdjointnessData.hamiltonianData.hamiltonianInputReady)) ∧
      (M.selfAdjointnessData.coreDenseForGraphInput ∧
        M.selfAdjointnessData.adjointDomainControlledInput ∧
          M.selfAdjointnessData.symmetricClosureInput ∧
            M.selfAdjointnessData.deficiencyIndexVanishingInput ∧
              M.selfAdjointnessData.selfAdjointnessInputReady)) ∧
      ((∀ a : r4HilbertSpectralTheoremTheoremParameter I TR M,
        r4HilbertSpectralTheoremTheoremProjectionFamily I TR M a) ∧
        M.spectralResolutionInput ∧ M.functionalCalculusInput ∧
          M.spectralMeasureCompatibilityInput ∧ M.selfAdjointOperatorInput ∧
            M.spectralTheoremInputReady) :=
  ⟨r4HilbertSpectralTheoremTheorem_self_adjointness_handoff I TR M,
    r4HilbertSpectralTheoremTheorem_bundle I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
