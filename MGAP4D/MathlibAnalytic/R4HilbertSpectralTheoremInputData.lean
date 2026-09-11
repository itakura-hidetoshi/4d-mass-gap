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

/-- Input data for a future spectral-theorem layer downstream of the R4
self-adjointness handoff.

The spectral objects are kept as abstract input obligations. This layer does not
prove self-adjointness from the preceding criterion, does not invoke a spectral
theorem, and does not state a spectral-gap result. -/
structure R4HilbertSpectralTheoremInputData where
  selfAdjointnessData : R4HilbertSelfAdjointnessInputData I TR
  spectralParameter : Type
  spectralProjectionFamily : spectralParameter → Prop
  spectralProjectionFamily_holds : ∀ a : spectralParameter, spectralProjectionFamily a
  spectralResolutionInput : Prop
  spectralResolutionInput_holds : spectralResolutionInput
  functionalCalculusInput : Prop
  functionalCalculusInput_holds : functionalCalculusInput
  spectralMeasureCompatibilityInput : Prop
  spectralMeasureCompatibilityInput_holds : spectralMeasureCompatibilityInput
  selfAdjointOperatorInput : Prop
  selfAdjointOperatorInput_holds : selfAdjointOperatorInput
  spectralTheoremInputReady : Prop
  spectralTheoremInputReady_holds : spectralTheoremInputReady

def r4HilbertSpectralTheoremInputSelfAdjointnessData
    (M : R4HilbertSpectralTheoremInputData I TR) :
    R4HilbertSelfAdjointnessInputData I TR :=
  M.selfAdjointnessData

def r4HilbertSpectralTheoremInputCarrier
    (M : R4HilbertSpectralTheoremInputData I TR) : Type :=
  r4HilbertSelfAdjointnessHandoffCarrier I TR M.selfAdjointnessData

def r4HilbertSpectralTheoremInputHamiltonianDomain
    (M : R4HilbertSpectralTheoremInputData I TR) : Type :=
  r4HilbertSelfAdjointnessHandoffHamiltonianDomain I TR M.selfAdjointnessData

def r4HilbertSpectralTheoremInputHamiltonianAction
    (M : R4HilbertSpectralTheoremInputData I TR) :
    r4HilbertSpectralTheoremInputHamiltonianDomain I TR M →
      r4HilbertSpectralTheoremInputCarrier I TR M :=
  r4HilbertSelfAdjointnessHandoffHamiltonianAction I TR M.selfAdjointnessData

def r4HilbertSpectralTheoremInputParameter
    (M : R4HilbertSpectralTheoremInputData I TR) : Type :=
  M.spectralParameter

def r4HilbertSpectralTheoremInputProjectionFamily
    (M : R4HilbertSpectralTheoremInputData I TR) :
    r4HilbertSpectralTheoremInputParameter I TR M → Prop :=
  M.spectralProjectionFamily

theorem r4HilbertSpectralTheoremInput_self_adjointness_handoff
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
  r4HilbertSelfAdjointnessHandoff_bundle I TR M.selfAdjointnessData

theorem r4HilbertSpectralTheoremInput_projection_family
    (M : R4HilbertSpectralTheoremInputData I TR)
    (a : r4HilbertSpectralTheoremInputParameter I TR M) :
    r4HilbertSpectralTheoremInputProjectionFamily I TR M a :=
  M.spectralProjectionFamily_holds a

theorem r4HilbertSpectralTheoremInput_resolution
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.spectralResolutionInput :=
  M.spectralResolutionInput_holds

theorem r4HilbertSpectralTheoremInput_functional_calculus
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.functionalCalculusInput :=
  M.functionalCalculusInput_holds

theorem r4HilbertSpectralTheoremInput_measure_compatibility
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.spectralMeasureCompatibilityInput :=
  M.spectralMeasureCompatibilityInput_holds

theorem r4HilbertSpectralTheoremInput_self_adjoint_operator
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.selfAdjointOperatorInput :=
  M.selfAdjointOperatorInput_holds

theorem r4HilbertSpectralTheoremInput_ready
    (M : R4HilbertSpectralTheoremInputData I TR) :
    M.spectralTheoremInputReady :=
  M.spectralTheoremInputReady_holds

theorem r4HilbertSpectralTheoremInput_bundle
    (M : R4HilbertSpectralTheoremInputData I TR) :
    (∀ a : r4HilbertSpectralTheoremInputParameter I TR M,
      r4HilbertSpectralTheoremInputProjectionFamily I TR M a) ∧
      M.spectralResolutionInput ∧ M.functionalCalculusInput ∧
        M.spectralMeasureCompatibilityInput ∧ M.selfAdjointOperatorInput ∧
          M.spectralTheoremInputReady :=
  ⟨r4HilbertSpectralTheoremInput_projection_family I TR M,
    r4HilbertSpectralTheoremInput_resolution I TR M,
    r4HilbertSpectralTheoremInput_functional_calculus I TR M,
    r4HilbertSpectralTheoremInput_measure_compatibility I TR M,
    r4HilbertSpectralTheoremInput_self_adjoint_operator I TR M,
    r4HilbertSpectralTheoremInput_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
