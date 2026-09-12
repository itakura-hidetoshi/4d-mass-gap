import MGAP4D.MathlibAnalytic.R4HilbertCompletedDenseRangeData
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

def r4HilbertCompletedActualCarrier
    (M : R4HilbertCompletedDenseRangeData I TR) : Type :=
  M.completedData.completedHilbertCarrier

def r4HilbertCompletedActualPreCarrier
    (M : R4HilbertCompletedDenseRangeData I TR) : Type :=
  M.completedData.preCompletionData.preHilbertCarrier

def r4HilbertCompletedActualNormedAddCommGroup
    (M : R4HilbertCompletedDenseRangeData I TR) :
    NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
  M.completedData.instNormedAddCommGroup

def r4HilbertCompletedActualNormedSpaceReal
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    NormedSpace ℝ (r4HilbertCompletedActualCarrier I TR M)) :=
  M.completedData.instNormedSpaceReal

def r4HilbertCompletedActualInnerProductSpaceReal
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    letI : NormedSpace ℝ (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedSpaceReal I TR M
    InnerProductSpace ℝ (r4HilbertCompletedActualCarrier I TR M)) :=
  M.completedData.instInnerProductSpaceReal

def r4HilbertCompletedActualCompleteSpace
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertCompletedActualCarrier I TR M)) :=
  M.completedData.instCompleteSpace

def r4HilbertCompletedActualPreMap
    (M : R4HilbertCompletedDenseRangeData I TR) :
    r4HilbertCompletedActualPreCarrier I TR M →
      r4HilbertCompletedActualCarrier I TR M :=
  M.completedData.preToCompleted

def r4HilbertCompletedActualQuotientMap
    (M : R4HilbertCompletedDenseRangeData I TR) :
    quotientCarrier I → r4HilbertCompletedActualCarrier I TR M :=
  M.completedData.quotientToCompleted

theorem r4HilbertCompletedActual_carrier_nonempty
    (M : R4HilbertCompletedDenseRangeData I TR) :
    Nonempty (r4HilbertCompletedActualCarrier I TR M) := by
  letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
    r4HilbertCompletedActualNormedAddCommGroup I TR M
  exact ⟨0⟩

theorem r4HilbertCompletedActual_pre_dense
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    DenseRange (r4HilbertCompletedActualPreMap I TR M)) :=
  r4HilbertCompletedDense_pre_dense_actual I TR M

theorem r4HilbertCompletedActual_quotient_dense
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    DenseRange (r4HilbertCompletedActualQuotientMap I TR M)) :=
  r4HilbertCompletedDense_quotient_dense_actual I TR M

theorem r4HilbertCompletedActual_pre_continuous
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    Continuous (r4HilbertCompletedActualPreMap I TR M)) :=
  r4HilbertCompletedDense_pre_continuous_actual I TR M

theorem r4HilbertCompletedActual_dense_bundle
    (M : R4HilbertCompletedDenseRangeData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M) :=
      M.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
      r4HilbertCompletedActualNormedAddCommGroup I TR M
    DenseRange (r4HilbertCompletedActualPreMap I TR M)) ∧
      (letI : NormedAddCommGroup (r4HilbertCompletedActualCarrier I TR M) :=
        r4HilbertCompletedActualNormedAddCommGroup I TR M
      DenseRange (r4HilbertCompletedActualQuotientMap I TR M)) :=
  ⟨r4HilbertCompletedActual_pre_dense I TR M,
    r4HilbertCompletedActual_quotient_dense I TR M⟩

theorem r4HilbertCompletedActual_route_ready
    (M : R4HilbertCompletedDenseRangeData I TR) :
    M.completedDenseRangeReady ∧ M.completedData.completedHilbertReady :=
  ⟨r4HilbertCompletedDense_completed_dense_ready I TR M,
    r4HilbertCompleted_hilbert_ready I TR M.completedData⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
