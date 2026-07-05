import MGAP4D.MathlibAnalytic.R4HilbertCompletedOSSemigroupTheoremAPI
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

/-- Handoff carrier for downstream generator layers: the completed R4 Hilbert
space on which the OS semigroup acts. -/
def r4HilbertCompletedOSSemigroupHandoffCarrier
    (M : R4HilbertCompletedOSSemigroupInputData I TR) : Type :=
  r4HilbertCompletedOSSemigroupTheoremCarrier I TR M

/-- Handoff time carrier for the completed R4 OS semigroup. -/
def r4HilbertCompletedOSSemigroupHandoffTimeCarrier
    (M : R4HilbertCompletedOSSemigroupInputData I TR) : Type :=
  r4HilbertCompletedOSSemigroupTheoremTimeCarrier I TR M

/-- Handoff zero time for the completed R4 OS semigroup. -/
def r4HilbertCompletedOSSemigroupHandoffZero
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    r4HilbertCompletedOSSemigroupHandoffTimeCarrier I TR M :=
  r4HilbertCompletedOSSemigroupTheoremZero I TR M

/-- Handoff time addition for the completed R4 OS semigroup. -/
def r4HilbertCompletedOSSemigroupHandoffAdd
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    r4HilbertCompletedOSSemigroupHandoffTimeCarrier I TR M →
      r4HilbertCompletedOSSemigroupHandoffTimeCarrier I TR M →
        r4HilbertCompletedOSSemigroupHandoffTimeCarrier I TR M :=
  r4HilbertCompletedOSSemigroupTheoremAdd I TR M

/-- Handoff action of the completed R4 OS semigroup. -/
def r4HilbertCompletedOSSemigroupHandoffAction
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    r4HilbertCompletedOSSemigroupHandoffTimeCarrier I TR M →
      r4HilbertCompletedOSSemigroupHandoffCarrier I TR M →
        r4HilbertCompletedOSSemigroupHandoffCarrier I TR M :=
  r4HilbertCompletedOSSemigroupTheoremAction I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_identity
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osIdentityLaw :=
  r4HilbertCompletedOSSemigroupTheorem_identity I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_semigroup_law
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osSemigroupLaw :=
  r4HilbertCompletedOSSemigroupTheorem_semigroup_law I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_contraction
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osContractionLaw :=
  r4HilbertCompletedOSSemigroupTheorem_contraction I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_strong_continuity
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osStrongContinuity :=
  r4HilbertCompletedOSSemigroupTheorem_strong_continuity I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_compatible
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osCompatibleWithHandoff :=
  r4HilbertCompletedOSSemigroupTheorem_compatible I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_ready
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osSemigroupReady :=
  r4HilbertCompletedOSSemigroupTheorem_ready I TR M

theorem r4HilbertCompletedOSSemigroupHandoff_laws
    (M : R4HilbertCompletedOSSemigroupInputData I TR) :
    M.osIdentityLaw ∧ M.osSemigroupLaw ∧ M.osContractionLaw ∧
      M.osStrongContinuity ∧ M.osCompatibleWithHandoff ∧ M.osSemigroupReady :=
  r4HilbertCompletedOSSemigroupTheorem_bundle I TR M

/-- Handoff theorem for the completed R4 OS semigroup.

This theorem packages the completed Hilbert-space handoff together with the OS
semigroup structural laws. It is intentionally still before the generator,
Hamiltonian, spectral theorem, and spectral-gap layers. -/
theorem r4HilbertCompletedOSSemigroupHandoff_constructed
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
  r4HilbertCompletedOSSemigroupTheorem_constructed I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
