import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicSecondVisitRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectRenewal
import Mathlib.Tactic

/-!
# Terminal sweep-stage profile and six-color renewal

PR #4892 proves the fixed-color energy renewal

  defect(f) = pathLoss(S f) + defect(S f).

PRs #4894--#4895 expose every second-sweep stage on the exact cyclic
between-visits bounded-concrete carrier.

This file packages the corresponding second-sweep local amplitudes as a named
terminal profile.  Its squared link energy is identified exactly, with the
same six-color normalization, with the mean terminal sweep path loss appearing
in the renewal law.

We also average the fixed-color PR #4892 renewal over the six spatial colors:

  defectMean(f)
    = terminalSweepPathLoss(f) + nextDefectMean(f).

No estimate, commutativity assumption, response symmetry, finite-cardinality
factor, or new coefficient is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance sweepBlockDefectTerminalProfileRenewalSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-color second-sweep local profile: evaluate the canonical one-link
stage profile on the first terminal sweep vector. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    PeriodicHypercubicEvenFixedSpatialColorLink H color → ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
    H N hN beta hbeta color
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
      H N hN beta hbeta color f)

/-- The fixed-color terminal profile is pointwise nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f e := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_nonneg
      H N hN beta hbeta color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color f) e

/-- Exact fixed-color energy identity for the terminal profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_sq_sum_eq_terminalSweepPathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f e ^ 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta color
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
      H N hN beta hbeta color
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta color f)

/-- Genuine spatial-link terminal profile.  Each link uses the terminal sweep
vector of its own six-spatial color. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
    H N hN beta hbeta
    (periodicHypercubicEvenSpatialSliceLinkColor H e) f
    ⟨e, rfl⟩

/-- The genuine spatial-link terminal profile is pointwise nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta f e := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_nonneg
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceLinkColor H e) f ⟨e, rfl⟩

/-- Reindexing the terminal profile over genuine spatial links gives exactly
the sum of the six fixed-color terminal sweep path losses. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_sq_sum_eq_colorTerminalSweepPathLossSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2) =
      ∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) := by
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2) =
        ∑ z :
            (Σ color : PeriodicHypercubicEvenGroundStateSpatialColor,
              PeriodicHypercubicEvenFixedSpatialColorLink H color),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
            H N hN beta hbeta z.1 f z.2 ^ 2 := by
      refine Fintype.sum_equiv
        (periodicHypercubicEvenSpatialSliceLinkEquivSigmaFixedSpatialColor H)
        _ _ ?_
      intro e
      rfl
    _ =
        ∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
          ∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
              H N hN beta hbeta color f e ^ 2 := by
      simpa using
        (Fintype.sum_sigma'
          (fun color : PeriodicHypercubicEvenGroundStateSpatialColor =>
            fun e : PeriodicHypercubicEvenFixedSpatialColorLink H color =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
                H N hN beta hbeta color f e ^ 2))
    _ =
        ∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta color
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f) := by
      apply Finset.sum_congr rfl
      intro color _hcolor
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_sq_sum_eq_terminalSweepPathLoss
          H N hN beta hbeta color f

/-- Six-color normalized terminal sweep path loss. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ c : Fin 6,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)

/-- Exact normalization: the terminal link-profile energy is the normalized
six-color terminal sweep path loss. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_normalized_sq_sum_eq_terminalSweepPathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (1 / 6 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
            H N hN beta hbeta f e ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
        H N hN beta hbeta f := by
  have hColorReindex :
      (∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f)) =
        ∑ c : Fin 6,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f) := by
    refine Fintype.sum_equiv
      periodicHypercubicEvenGroundStateSpatialColorEquivFin
      _ _ ?_
    intro color
    simp
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_sq_sum_eq_colorTerminalSweepPathLossSum
      H N hN beta hbeta f,
    hColorReindex]
  rfl

/-- Mean squared defect remaining after applying one additional complete sweep
inside each of the six colors. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ c : Fin 6,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
          H N hN beta hbeta
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)‖ ^ 2

/-- Six-color averaged exact renewal:
current mean defect = terminal sweep path loss + next mean defect. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_eq_terminalSweepPathLoss_add_nextDefectMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
        H N hN beta hbeta f =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
          H N hN beta hbeta f +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
          H N hN beta hbeta f := by
  have hEach :
      ∀ c : Fin 6,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 =
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f) +
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)‖ ^ 2 := by
    intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalSweepPathLoss_add_nextDefect_norm_sq
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  have hSum :
      (∑ c : Fin 6,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) =
        (∑ c : Fin 6,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)) +
          ∑ c : Fin 6,
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
              H N hN beta hbeta
              (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)‖ ^ 2 := by
    calc
      (∑ c : Fin 6,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) =
          ∑ c : Fin 6,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                  H N hN beta hbeta
                  (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f) +
              ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
                H N hN beta hbeta
                (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
                  H N hN beta hbeta
                  (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f)‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact hEach c
      _ = _ := by
        rw [Finset.sum_add_distrib]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkNextSweepBlockDefectMeanNormSq
  rw [hSum]
  ring

end

end MGAP4D.MathlibAnalytic
