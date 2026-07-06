import MGAP4D.MathlibAnalytic.R4HilbertCompletedOSSemigroupHandoffAPI
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

/-- Input data for the infinitesimal generator associated with the completed R4
OS semigroup.

The domain is kept as explicit graph data. This layer does not identify the
generator as a physical Hamiltonian, does not assert self-adjointness, and does
not state a spectral-gap theorem. -/
structure R4HilbertOSGeneratorInputData where
  semigroupData : R4HilbertCompletedOSSemigroupInputData I TR
  generatorDomain : Type
  generatorDomainToHilbert :
    generatorDomain → r4HilbertCompletedOSSemigroupHandoffCarrier I TR semigroupData
  generatorAction :
    generatorDomain → r4HilbertCompletedOSSemigroupHandoffCarrier I TR semigroupData
  generatorDomainDense : Prop
  generatorDomainDense_holds : generatorDomainDense
  generatorGraphClosed : Prop
  generatorGraphClosed_holds : generatorGraphClosed
  generatorCompatibleWithSemigroup : Prop
  generatorCompatibleWithSemigroup_holds : generatorCompatibleWithSemigroup
  generatorDissipativeEstimate : Prop
  generatorDissipativeEstimate_holds : generatorDissipativeEstimate
  generatorInputReady : Prop
  generatorInputReady_holds : generatorInputReady

def r4HilbertOSGeneratorInputSemigroupData
    (M : R4HilbertOSGeneratorInputData I TR) :
    R4HilbertCompletedOSSemigroupInputData I TR :=
  M.semigroupData

def r4HilbertOSGeneratorInputCarrier
    (M : R4HilbertOSGeneratorInputData I TR) : Type :=
  r4HilbertCompletedOSSemigroupHandoffCarrier I TR M.semigroupData

def r4HilbertOSGeneratorInputDomain
    (M : R4HilbertOSGeneratorInputData I TR) : Type :=
  M.generatorDomain

def r4HilbertOSGeneratorInputDomainMap
    (M : R4HilbertOSGeneratorInputData I TR) :
    r4HilbertOSGeneratorInputDomain I TR M → r4HilbertOSGeneratorInputCarrier I TR M :=
  M.generatorDomainToHilbert

def r4HilbertOSGeneratorInputAction
    (M : R4HilbertOSGeneratorInputData I TR) :
    r4HilbertOSGeneratorInputDomain I TR M → r4HilbertOSGeneratorInputCarrier I TR M :=
  M.generatorAction

theorem r4HilbertOSGeneratorInput_semigroup_handoff
    (M : R4HilbertOSGeneratorInputData I TR) :
    ((Nonempty
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.semigroupData.handoffData
      InnerProductSpace ℝ (r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData)) ∧
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.semigroupData.handoffData
      CompleteSpace (r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData)) ∧
        (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData) :=
          r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.semigroupData.handoffData
        DenseRange (r4HilbertCompletedHilbertSpaceHandoffPreMap I TR M.semigroupData.handoffData)) ∧
          (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData) :=
            r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M.semigroupData.handoffData
          DenseRange (r4HilbertCompletedHilbertSpaceHandoffQuotientMap I TR M.semigroupData.handoffData)) ∧
            r4HilbertCompletedHilbertSpace I TR M.semigroupData.handoffData =
              (letI : NormedAddCommGroup
                  (r4HilbertCompletedActualPreCarrier I TR M.semigroupData.handoffData.routeData) :=
                M.semigroupData.handoffData.routeData.completedData.preCompletionData.instNormedAddCommGroup
              UniformSpace.Completion
                (r4HilbertCompletedActualPreCarrier I TR M.semigroupData.handoffData.routeData))) ∧
      (∀ q : quotientCarrier I,
        r4HilbertCompletedHilbertSpaceHandoffQuotientMap I TR M.semigroupData.handoffData q =
          r4HilbertCompletedHilbertSpaceHandoffPreMap I TR M.semigroupData.handoffData
            (M.semigroupData.handoffData.routeData.completedData.preCompletionData.quotientToPreHilbert q)) ∧
        (M.semigroupData.handoffData.routeData.completedData.preCompletionData.preCompletionReady ∧
          M.semigroupData.handoffData.routeData.completedData.completedHilbertReady ∧
            M.semigroupData.handoffData.routeData.completedDenseRangeReady ∧
              M.semigroupData.handoffData.quotientToStandardDenseReady)) ∧
      (M.semigroupData.osIdentityLaw ∧ M.semigroupData.osSemigroupLaw ∧
        M.semigroupData.osContractionLaw ∧ M.semigroupData.osStrongContinuity ∧
          M.semigroupData.osCompatibleWithHandoff ∧ M.semigroupData.osSemigroupReady) :=
  r4HilbertCompletedOSSemigroupHandoff_constructed I TR M.semigroupData

theorem r4HilbertOSGeneratorInput_domain_dense
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDomainDense :=
  M.generatorDomainDense_holds

theorem r4HilbertOSGeneratorInput_graph_closed
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorGraphClosed :=
  M.generatorGraphClosed_holds

theorem r4HilbertOSGeneratorInput_compatible_with_semigroup
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorCompatibleWithSemigroup :=
  M.generatorCompatibleWithSemigroup_holds

theorem r4HilbertOSGeneratorInput_dissipative_estimate
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDissipativeEstimate :=
  M.generatorDissipativeEstimate_holds

theorem r4HilbertOSGeneratorInput_ready
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorInputReady :=
  M.generatorInputReady_holds

theorem r4HilbertOSGeneratorInput_bundle
    (M : R4HilbertOSGeneratorInputData I TR) :
    M.generatorDomainDense ∧ M.generatorGraphClosed ∧
      M.generatorCompatibleWithSemigroup ∧ M.generatorDissipativeEstimate ∧
        M.generatorInputReady :=
  ⟨r4HilbertOSGeneratorInput_domain_dense I TR M,
    r4HilbertOSGeneratorInput_graph_closed I TR M,
    r4HilbertOSGeneratorInput_compatible_with_semigroup I TR M,
    r4HilbertOSGeneratorInput_dissipative_estimate I TR M,
    r4HilbertOSGeneratorInput_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
