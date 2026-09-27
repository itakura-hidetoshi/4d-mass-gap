import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointFixedColorSweepVectorTelescoping
import Mathlib.Tactic

/-!
# Exact stage residual behind the canonical sweep local profile

The generic stage profile allows repeated labels, so its amplitude at a label
is defined as the square root of the sum of all residual squares carrying that
label. The canonical one-link sweep uses Finset.univ.toList, hence is
duplicate-free. Therefore every link occurs exactly once and its local
profile is not merely an upper bound: it is exactly the norm of the residual
vector at that canonical stage.

This file proves that fact in two layers.

First, for an arbitrary ordered sweep:
* a label absent from the list has zero squared stage profile;
* if cs = pre ++ d :: suffix and d occurs in neither side, the squared
  profile at d is exactly the squared norm of the residual after pre;
* the corresponding amplitude is exactly that residual norm.

Second, the theorem is specialized to the canonical fixed-color and genuine
spatial-link profiles used by the six-spatial Schur receiver.

No probability, response, influence, or coercivity estimate is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A label absent from an ordered sweep has zero attributed squared residual
mass. -/
theorem realHilbertProjectionSweepStageResidualSqProfile_eq_zero_of_not_mem
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E)
    (d : C)
    (hd : d ∉ cs) :
    realHilbertProjectionSweepStageResidualSqProfile P cs x d = 0 := by
  induction cs generalizing x with
  | nil =>
      simp [realHilbertProjectionSweepStageResidualSqProfile]
  | cons c cs ih =>
      have hdc : d ≠ c := by
        intro h
        apply hd
        simp [h]
      have htail : d ∉ cs := by
        intro h
        apply hd
        simp [h]
      simp [
        realHilbertProjectionSweepStageResidualSqProfile,
        hdc,
        ih (P c x) htail]

/-- If a label occurs exactly once at pre ++ d :: suffix, its entire squared
stage profile is the squared norm of the residual at that stage. -/
theorem realHilbertProjectionSweepStageResidualSqProfile_append_cons_eq_norm_sq
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (x : E)
    (d : C)
    (hpre : d ∉ pre)
    (hsuffix : d ∉ suffix) :
    realHilbertProjectionSweepStageResidualSqProfile
        P (pre ++ d :: suffix) x d =
      ‖realHilbertProjectionSweep P pre x -
          P d (realHilbertProjectionSweep P pre x)‖ ^ 2 := by
  induction pre generalizing x with
  | nil =>
      have hzero :
          realHilbertProjectionSweepStageResidualSqProfile
              P suffix (P d x) d = 0 :=
        realHilbertProjectionSweepStageResidualSqProfile_eq_zero_of_not_mem
          P suffix (P d x) d hsuffix
      simp [
        realHilbertProjectionSweepStageResidualSqProfile,
        realHilbertProjectionSweep,
        hzero]
  | cons c pre ih =>
      have hdc : d ≠ c := by
        intro h
        apply hpre
        simp [h]
      have htail : d ∉ pre := by
        intro h
        apply hpre
        simp [h]
      simpa [
        realHilbertProjectionSweepStageResidualSqProfile,
        realHilbertProjectionSweep,
        hdc] using
        (ih (x := P c x) htail)

/-- Singleton-occurrence amplitude form of the preceding exact identity. -/
theorem realHilbertProjectionSweepStageResidualAmplitude_append_cons_eq_norm
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (x : E)
    (d : C)
    (hpre : d ∉ pre)
    (hsuffix : d ∉ suffix) :
    realHilbertProjectionSweepStageResidualAmplitude
        P (pre ++ d :: suffix) x d =
      ‖realHilbertProjectionSweep P pre x -
          P d (realHilbertProjectionSweep P pre x)‖ := by
  unfold realHilbertProjectionSweepStageResidualAmplitude
  rw [
    realHilbertProjectionSweepStageResidualSqProfile_append_cons_eq_norm_sq
      P pre suffix x d hpre hsuffix]
  exact Real.sqrt_sq (norm_nonneg _)

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

local instance sweepStageExactResidualSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The canonical fixed-color local profile at a link is exactly the norm of
the one-link residual at the preserved canonical prefix. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix)
    (hFresh : e ∉ pre) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
        H N hN beta hbeta color f e =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color pre f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color e
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color pre f)‖ := by
  have hNodup :
      (pre ++ e :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hTailNodup : (e :: suffix).Nodup :=
    hNodup.of_append_right
  have hSuffix : e ∉ suffix :=
    (List.nodup_cons.mp hTailNodup).1
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
  rw [hSplit]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector] using
    realHilbertProjectionSweepStageResidualAmplitude_append_cons_eq_norm
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      pre suffix f e hFresh hSuffix

/-- Ordinary spatial-link wrapper of the exact canonical stage residual norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (pre suffix :
      List
        (PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e)))
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset
          (PeriodicHypercubicEvenFixedSpatialColorLink H
            (periodicHypercubicEvenSpatialSliceLinkColor H e))).toList =
          pre ++
            (⟨e, rfl⟩ :
              PeriodicHypercubicEvenFixedSpatialColorLink H
                (periodicHypercubicEvenSpatialSliceLinkColor H e)) ::
              suffix)
    (hFresh :
      (⟨e, rfl⟩ :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e)) ∉ pre) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta
          (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta
          (periodicHypercubicEvenSpatialSliceLinkColor H e)
          (⟨e, rfl⟩ :
            PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e))
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta
            (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f)‖ := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_eq_stageResidual_norm_of_canonicalPrefix
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceLinkColor H e)
      pre suffix
      (⟨e, rfl⟩ :
        PeriodicHypercubicEvenFixedSpatialColorLink H
          (periodicHypercubicEvenSpatialSliceLinkColor H e))
      f hSplit hFresh

end

end MathlibAnalytic
end MGAP4D
