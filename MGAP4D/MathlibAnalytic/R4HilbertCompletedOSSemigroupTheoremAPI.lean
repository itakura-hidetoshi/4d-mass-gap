import MGAP4D.MathlibAnalytic.R4HilbertCompletedOSSemigroupInputData
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

def r4HilbertCompletedOSSemigroupTheoremHandoffData
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    R4HilbertStandardCompletionQuotientDenseData I TR :=
  r4HilbertCompletedOSSemigroupInputHandoffData I TR M

def r4HilbertCompletedOSSemigroupTheoremCarrier
    (M : R4HilbertCompletedOSSemigroupInputData I TR) : Type :=
  r4HilbertCompletedOSSemigroupInputCarrier I TR M

def r4HilbertCompletedOSSemigroupTheoremTimeCarrier
    (M : R4HilbertCompletedOSSemigroupInputData I TR) : Type :=
  M.osTimeCarrier

def r4HilbertCompletedOSSemigroupTheoremZero
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    r4HilbertCompletedOSSemigroupTheoremTimeCarrier I TR M :=
  M.osTimeZero

def r4HilbertCompletedOSSemigroupTheoremAdd
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    r4HilbertCompletedOSSemigroupTheoremTimeCarrier I TR M →
      r4HilbertCompletedOSSemigroupTheoremTimeCarrier I TR M →
        r4HilbertCompletedOSSemigroupTheoremTimeCarrier I TR M :=
  M.osTimeAdd

def r4HilbertCompletedOSSemigroupTheoremAction
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    r4HilbertCompletedOSSemigroupTheoremTimeCarrier I TR M →
      r4HilbertCompletedOSSemigroupTheoremCarrier I TR M →
        r4HilbertCompletedOSSemigroupTheoremCarrier I TR M :=
  r4HilbertCompletedOSSemigroupInputAction I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_handoff_constructed
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    (Nonempty
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
      InnerProductSpace ℝ (r4HilbertCompletedHilbertSpace I TR M.handoffData)) ∧
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
      CompleteSpace (r4HilbertCompletedHilbertSpace I TR M.handoffData)) ∧
        (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
          r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
        DenseRange (r4HilbertCompletedHilbertSpaceHandoffPreMap I TR M.handoffData)) ∧
          (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
            r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
          DenseRange (r4HilbertCompletedHilbertSpaceHandoffQuotientMap I TR M.handoffData)) ∧
            r4HilbertCompletedHilbertSpace I TR M.handoffData =
              (letI : NormedAddCommGroup
                  (r4HilbertCompletedActualPreCarrier I TR M.handoffData.routeData) :=
                M.handoffData.routeData.completedData.preCompletionData.instNormedAddCommGroup
              UniformSpace.Completion
                (r4HilbertCompletedActualPreCarrier I TR M.handoffData.routeData))) ∧
      (∀ q : quotientCarrier I,
        r4HilbertCompletedHilbertSpaceHandoffQuotientMap I TR M.handoffData q =
          r4HilbertCompletedHilbertSpaceHandoffPreMap I TR M.handoffData
            (M.handoffData.routeData.completedData.preCompletionData.quotientToPreHilbert q)) ∧
        (M.handoffData.routeData.completedData.preCompletionData.preCompletionReady ∧
          M.handoffData.routeData.completedData.completedHilbertReady ∧
            M.handoffData.routeData.completedDenseRangeReady ∧
              M.handoffData.quotientToStandardDenseReady) :=
  r4HilbertCompletedOSSemigroupInput_handoff_constructed I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_identity
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osIdentityLaw :=
  r4HilbertCompletedOSSemigroupInput_identity I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_semigroup_law
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osSemigroupLaw :=
  r4HilbertCompletedOSSemigroupInput_semigroup_law I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_contraction
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osContractionLaw :=
  r4HilbertCompletedOSSemigroupInput_contraction I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_strong_continuity
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osStrongContinuity :=
  r4HilbertCompletedOSSemigroupInput_strong_continuity I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_compatible
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osCompatibleWithHandoff :=
  r4HilbertCompletedOSSemigroupInput_compatible I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_ready
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osSemigroupReady :=
  r4HilbertCompletedOSSemigroupInput_ready I TR M

theorem r4HilbertCompletedOSSemigroupTheorem_bundle
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osIdentityLaw ∧ M.osSemigroupLaw ∧ M.osContractionLaw ∧
      M.osStrongContinuity ∧ M.osCompatibleWithHandoff ∧ M.osSemigroupReady :=
  r4HilbertCompletedOSSemigroupInput_bundle I TR M

/-- The theorem API handoff for an OS semigroup on the completed R4 Hilbert
space. This packages the already-constructed completed Hilbert-space handoff
with the OS semigroup laws recorded as data, without introducing a generator,
Hamiltonian, spectral theorem, or gap statement. -/
theorem r4HilbertCompletedOSSemigroupTheorem_constructed
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    ((Nonempty
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
      InnerProductSpace ℝ (r4HilbertCompletedHilbertSpace I TR M.handoffData)) ∧
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
      CompleteSpace (r4HilbertCompletedHilbertSpace I TR M.handoffData)) ∧
        (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
          r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
        DenseRange (r4HilbertCompletedHilbertSpaceHandoffPreMap I TR M.handoffData)) ∧
          (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.handoffData) :=
            r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.handoffData
          DenseRange (r4HilbertCompletedHilbertSpaceHandoffQuotientMap I TR M.handoffData)) ∧
            r4HilbertCompletedHilbertSpace I TR M.handoffData =
              (letI : NormedAddCommGroup
                  (r4HilbertCompletedActualPreCarrier I TR M.handoffData.routeData) :=
                M.handoffData.routeData.completedData.preCompletionData.instNormedAddCommGroup
              UniformSpace.Completion
                (r4HilbertCompletedActualPreCarrier I TR M.handoffData.routeData))) ∧
      (∀ q : quotientCarrier I,
        r4HilbertCompletedHilbertSpaceHandoffQuotientMap I TR M.handoffData q =
          r4HilbertCompletedHilbertSpaceHandoffPreMap I TR M.handoffData
            (M.handoffData.routeData.completedData.preCompletionData.quotientToPreHilbert q)) ∧
        (M.handoffData.routeData.completedData.preCompletionData.preCompletionReady ∧
          M.handoffData.routeData.completedData.completedHilbertReady ∧
            M.handoffData.routeData.completedDenseRangeReady ∧
              M.handoffData.quotientToStandardDenseReady)) ∧
      (M.osIdentityLaw ∧ M.osSemigroupLaw ∧ M.osContractionLaw ∧
        M.osStrongContinuity ∧ M.osCompatibleWithHandoff ∧ M.osSemigroupReady) :=
  ⟨r4HilbertCompletedOSSemigroupTheorem_handoff_constructed I TR M,
    r4HilbertCompletedOSSemigroupTheorem_bundle I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
