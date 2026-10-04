import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkOscillationResidualUpper
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageProfileCoreClosure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepStageLocalProfileExactResidual
import Mathlib.Tactic

/-!
# Sweep-stage profile energy from concrete link oscillations

PR #5143 proves the one-link upper direction on the bounded-concrete carrier:

  concrete target-link oscillation <= delta
    ==> ||f - P_target f||^2 <= delta^2.

The six-spatial sweep-stage profile is evaluated not at the initial vector but
at the successive canonical fixed-color sweep stages.  This file packages the
exact data needed at each such stage.

For every genuine spatial link e, choose a bounded concrete representative of
the corresponding canonical stage vector and a target-link oscillation bound
delta(e).  The exact stage-residual theorem then gives

  localProfile(e)^2 <= delta(e)^2.

Summing over the genuine link carrier yields

  ProfileEnergy(f) <= (1/6) * sum_e delta(e)^2.

A second layer lets delta depend on the ambient joint-L2 vector.  If every
coordinate delta_e(f) is continuous in f and the stage-oscillation construction
is available on the dense bounded-concrete core, PR #5141 extends the resulting
quadratic majorant to every genuine joint-L2 vector with no coefficient loss.

This is a receiver.  It does not assert that the Dobrushin variation profile is
already continuous in the L2 topology, nor that every L2 vector has a bounded
continuous representative.  No transfer identification, Euclidean-time
interpretation, or H1-D5 exact descent is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

local instance groundStateSweepStageOscillationMajorantSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- At each genuine spatial link, one can choose a bounded concrete
representative of the exact canonical sweep-stage vector whose oscillation in
that selected link is bounded by the declared profile value. -/
def
    PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (delta : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) : Prop :=
  ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ∃
      (pre suffix :
        List
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e)))
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
        (Finset.univ :
          Finset
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
            pre ++
              (⟨e, rfl⟩ :
                PeriodicHypercubicEvenFixedSpatialColorLink H
                  (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
                suffix ∧
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
            H N hN beta hbeta F hF bound hbound =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f ∧
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteOscillationBoundedBy
          H N e F (delta e)

/-- Normalized squared oscillation energy on the genuine spatial-link carrier. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
    (H : ℕ)
    (delta : PeriodicHypercubicEvenSpatialSliceLink H → ℝ) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, delta e ^ 2

/-- One canonical split of a duplicate-free fixed-color enumeration is fresh
on its prefix. -/
private theorem groundStateSweepStageOscillationMajorant_canonicalSplit_fresh
    (H : ℕ)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix) :
    e ∉ pre := by
  have hNodup : (pre ++ e :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hMiddle : (e :: (pre ++ suffix)).Nodup :=
    List.nodup_middle.mp hNodup
  have hNot : e ∉ pre ++ suffix :=
    hMiddle.notMem
  intro he
  exact hNot (by simp [he])

/-- Stagewise concrete oscillation bounds dominate every squared entry of the
genuine six-spatial sweep-stage profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageLocalProfile_sq_le_of_concreteOscillationProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (delta : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hdelta : ∀ e, 0 ≤ delta e)
    (hOsc :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
        H N hN beta hbeta f delta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2 ≤
      delta e ^ 2 := by
  rcases hOsc e with
    ⟨pre, suffix, F, hF, bound, hbound, hSplit, hRep, hFOsc⟩
  have hFresh :
      (⟨e, rfl⟩ :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre :=
    groundStateSweepStageOscillationMajorant_canonicalSplit_fresh
      H
      (periodicHypercubicEvenSpatialSliceLinkColor H e)
      pre suffix
      (⟨e, rfl⟩ :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e))
      hSplit
  have hProfile :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      H N hN beta hbeta e pre suffix f hSplit hFresh
  have hResidual :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_condExpL2_residual_sq_le_of_oscillation
      H N hN beta hbeta e F hF bound hbound
      (delta e) (hdelta e) hFOsc
  rw [hProfile]
  rw [← hRep]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
  ] using hResidual

/-- Normalized oscillation-energy bound for the complete genuine sweep-stage
profile.  There is no spatial-link cardinality factor beyond the existing
six-color normalization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_oscillationEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (delta : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hdelta : ∀ e, 0 ≤ delta e)
    (hOsc :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
        H N hN beta hbeta f delta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
        H N hN beta hbeta f ≤
      periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
        H delta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
  have hSum :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f e ^ 2) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, delta e ^ 2 := by
    exact Finset.sum_le_sum fun e _ =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageLocalProfile_sq_le_of_concreteOscillationProfile
        H N hN beta hbeta f delta hdelta hOsc e
  exact mul_le_mul_of_nonneg_left hSum (by norm_num)

/-- L2-dependent normalized oscillation-energy majorant. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (delta :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
    H (delta f)

/-- Coordinatewise continuity of an L2-dependent oscillation profile implies
continuity of its normalized squared energy. -/
theorem
    continuous_periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (delta :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hdeltaContinuous :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        Continuous (fun f => delta f e)) :
    Continuous
      (periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
        H N hN beta hbeta delta) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy
  apply continuous_const.mul
  apply continuous_finset_sum
  intro e _he
  exact (hdeltaContinuous e).pow 2

/-- If a coordinatewise continuous oscillation profile controls every canonical
sweep stage on the dense bounded-concrete core, its normalized squared energy
controls the sweep-stage profile on the whole genuine joint L2 carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_oscillationMajorant_of_boundedConcreteCore
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (delta :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hdeltaNonneg :
      ∀ f e, 0 ≤ delta f e)
    (hdeltaContinuous :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        Continuous (fun f => delta f e))
    (hCoreOsc :
      ∀ f,
        f ∈
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
              H N hN beta hbeta →
          PeriodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageConcreteOscillationProfileBoundedBy
            H N hN beta hbeta f (delta f)) :
    ∀ f,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy
          H N hN beta hbeta f ≤
        periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
          H N hN beta hbeta delta f := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_of_boundedConcreteCore
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
        H N hN beta hbeta delta)
      (continuous_periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationMajorant
        H N hN beta hbeta delta hdeltaContinuous)
  intro f hf
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfileEnergy_le_oscillationEnergy
      H N hN beta hbeta f (delta f)
      (hdeltaNonneg f) (hCoreOsc f hf)

end

end MathlibAnalytic
end MGAP4D
