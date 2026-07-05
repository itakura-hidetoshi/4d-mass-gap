import MGAP4D.MathlibAnalytic.R4HilbertCanonicalCompletionTheoremAPI
import Mathlib.Analysis.InnerProductSpace.Completion
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

/-- The standard mathlib completion carrier for the R4 pre-Hilbert carrier. -/
def r4HilbertStandardCompletionCarrier
    (M : R4HilbertCompletedDenseRangeData I TR) : Type :=
  UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M)

/-- The canonical coercion of the R4 pre-Hilbert carrier into its mathlib completion. -/
def r4HilbertStandardCompletionMap
    (M : R4HilbertCompletedDenseRangeData I TR) :
    r4HilbertCompletedActualPreCarrier I TR M →
      r4HilbertStandardCompletionCarrier I TR M :=
  fun x => by
    change UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M)
    letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    exact (x : UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M))

def r4HilbertStandardCompletionNormedAddCommGroup
    (M : R4HilbertCompletedDenseRangeData I TR) :
    NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M) := by
  letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
    M.completedData.preCompletionData.instNormedAddCommGroup
  change NormedAddCommGroup
    (UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M))
  exact UniformSpace.Completion.instNormedAddCommGroup
    (r4HilbertCompletedActualPreCarrier I TR M)

def r4HilbertStandardCompletionInnerProductSpaceReal
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M
    InnerProductSpace ℝ (r4HilbertStandardCompletionCarrier I TR M)) := by
  letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
    M.completedData.preCompletionData.instNormedAddCommGroup
  letI : NormedSpace ℝ (r4HilbertCompletedActualPreCarrier I TR M) :=
    M.completedData.preCompletionData.instNormedSpaceReal
  letI : InnerProductSpace ℝ (r4HilbertCompletedActualPreCarrier I TR M) :=
    M.completedData.preCompletionData.instInnerProductSpaceReal
  change InnerProductSpace ℝ
    (UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M))
  exact UniformSpace.Completion.innerProductSpace

theorem r4HilbertStandardCompletion_complete_space
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertStandardCompletionCarrier I TR M)) := by
  letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
    M.completedData.preCompletionData.instNormedAddCommGroup
  change CompleteSpace
    (UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M))
  exact UniformSpace.Completion.completeSpace
    (r4HilbertCompletedActualPreCarrier I TR M)

theorem r4HilbertStandardCompletion_dense
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M
    DenseRange (r4HilbertStandardCompletionMap I TR M)) := by
  letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
    M.completedData.preCompletionData.instNormedAddCommGroup
  change DenseRange
    (fun x : r4HilbertCompletedActualPreCarrier I TR M =>
      (x : UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M)))
  exact UniformSpace.Completion.denseRange_coe

theorem r4HilbertStandardCompletion_carrier_eq_uniform_completion
    (M : R4HilbertCompletedDenseRangeData I TR) :
    r4HilbertStandardCompletionCarrier I TR M =
      UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M) :=
  rfl

theorem r4HilbertStandardCompletion_map_eq_coe
    (M : R4HilbertCompletedDenseRangeData I TR)
    (x : r4HilbertCompletedActualPreCarrier I TR M) :
    r4HilbertStandardCompletionMap I TR M x =
      (x : UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M)) :=
  rfl

theorem r4HilbertStandardCompletion_complete_dense_bundle
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertStandardCompletionCarrier I TR M)) ∧
      (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M) :=
        r4HilbertStandardCompletionNormedAddCommGroup I TR M
      DenseRange (r4HilbertStandardCompletionMap I TR M)) :=
  ⟨r4HilbertStandardCompletion_complete_space I TR M,
    r4HilbertStandardCompletion_dense I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
