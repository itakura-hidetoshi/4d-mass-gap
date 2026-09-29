import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepStageProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectTerminalProfileRenewal
import Mathlib.Tactic

/-!
# Exact unique-stage realization of the canonical local profile

The generic sweep-stage profile allows repeated labels and therefore records,
for one label, the sum of every residual created at every occurrence.

The canonical fixed-color one-link sweep is different: it is
`Finset.univ.toList`, hence duplicate-free.  For a split

  canonicalList = pre ++ e :: suffix

the label `e` occurs exactly once.  Its stage-profile mass is therefore not
merely an upper bound for the residual at that stage: it is exactly that
residual norm squared.

This file records the generic unique-occurrence lemma and specializes it to
both the original and terminal fixed-color local profiles.  No commutativity
between distinct one-link projections is used.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance exactUniqueStageLocalProfileSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- If a label occurs exactly once in an ordered sweep, at
`pre ++ d :: suffix`, then its attributed squared stage-profile mass is
exactly the squared residual created at that single stage. -/
theorem realHilbertProjectionSweepStageResidualSqProfile_eq_norm_sq_append_cons_of_not_mem
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
      simp [realHilbertProjectionSweepStageResidualSqProfile,
        realHilbertProjectionSweep, hsuffix]
  | cons c pre ih =>
      have hdc : d ≠ c := by
        intro h
        apply hpre
        simp [h]
      have hpre' : d ∉ pre := by
        intro hd
        apply hpre
        simp [hd]
      simp only [List.cons_append,
        realHilbertProjectionSweepStageResidualSqProfile]
      rw [if_neg hdc]
      simp only [zero_add]
      simpa [realHilbertProjectionSweep] using
        ih (x := P c x) hpre' hsuffix

/-- Amplitude-squared form of the preceding unique-stage identity. -/
theorem realHilbertProjectionSweepStageResidualAmplitude_sq_eq_norm_sq_append_cons_of_not_mem
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
          P (pre ++ d :: suffix) x d ^ 2 =
      ‖realHilbertProjectionSweep P pre x -
          P d (realHilbertProjectionSweep P pre x)‖ ^ 2 := by
  rw [realHilbertProjectionSweepStageResidualAmplitude_sq]
  exact
    realHilbertProjectionSweepStageResidualSqProfile_eq_norm_sq_append_cons_of_not_mem
      P pre suffix x d hpre hsuffix

/-- On the duplicate-free canonical fixed-color list, the original local
profile at a chosen link is exactly the norm of that link's unique stage
residual, squared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_sq_eq_stageResidual_of_canonicalSplit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix)
    (hFresh : e ∉ pre) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
          H N hN beta hbeta color f e ^ 2 =
      ‖realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          pre f -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color e
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            pre f)‖ ^ 2 := by
  have hNoDup :
      (pre ++ e :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hTailNoDup : (e :: suffix).Nodup :=
    hNoDup.of_append_right
  have hSuffix : e ∉ suffix :=
    hTailNoDup.notMem
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
  rw [hSplit]
  exact
    realHilbertProjectionSweepStageResidualAmplitude_sq_eq_norm_sq_append_cons_of_not_mem
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      pre suffix f e hFresh hSuffix

/-- The same exact unique-stage identity for the terminal profile: the input
vector is the terminal first-sweep vector, but the canonical second-sweep list
is unchanged and remains duplicate-free. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_sq_eq_stageResidual_of_canonicalSplit
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix)
    (hFresh : e ∉ pre) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f e ^ 2 =
      ‖realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          pre
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color e
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            pre
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f))‖ ^ 2 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_sq_eq_stageResidual_of_canonicalSplit
      H N hN beta hbeta color pre suffix e
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color f)
      hSplit hFresh

end

end MGAP4D.MathlibAnalytic
