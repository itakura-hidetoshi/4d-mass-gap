import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepStageProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepPathLoss
import Mathlib.Tactic

/-!
# Ground-state six-spatial one-link sweep-stage local profile

This file realizes the path loss from the preceding six-color theorem as an
actual link-indexed nonnegative local profile.

Inside each spatial color, the canonical `Finset.univ.toList` one-link sweep
is followed stage by stage.  The residual amplitude attributed to a link is
the square root of the squared residual mass encountered at that link's sweep
stage.  The generic stage-profile identity gives exact equality between the
sum of squared local amplitudes and the fixed-color path loss.

The six color fibers are then reindexed back to the genuine spatial-link
carrier.  Consequently,

  (1/6) * sum_e localProfile(e)^2
    = sixSpatialOneLinkSweepPathLoss
    <= sixSpatialResidualEnergy.

No color-class cardinality factor appears.  The construction is valid on the
whole genuine ground-state joint L2 carrier, hence in particular on the
bounded-concrete core.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance groundStateSweepStageProfileSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Canonical equivalence between a spatial link and the dependent pair
consisting of its six-spatial color together with that link in the
corresponding color fiber. -/
def periodicHypercubicEvenSpatialSliceLinkEquivSigmaFixedSpatialColor
    (H : ℕ) :
    PeriodicHypercubicEvenSpatialSliceLink H ≃
      (Σ color : PeriodicHypercubicEvenGroundStateSpatialColor,
        PeriodicHypercubicEvenFixedSpatialColorLink H color) where
  toFun e :=
    ⟨periodicHypercubicEvenSpatialSliceLinkColor H e, ⟨e, rfl⟩⟩
  invFun z := z.2.1
  left_inv := by
    intro e
    rfl
  right_inv := by
    rintro ⟨color, ⟨e, hColor⟩⟩
    dsimp
    subst color
    rfl

/-- Fixed-color receiver-ready local amplitude obtained from the actual
successive residuals along the canonical one-link sweep. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    PeriodicHypercubicEvenFixedSpatialColorLink H color → ℝ :=
  realHilbertProjectionSweepStageResidualAmplitude
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color)
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
    f

/-- The fixed-color sweep-stage local profile is pointwise nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
        H N hN beta hbeta color f e := by
  exact
    realHilbertProjectionSweepStageResidualAmplitude_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
      f e

/-- Exact fixed-color energy identity: squared local amplitudes sum to the
same ordered path loss used by the nested-block theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
        H N hN beta hbeta color f e ^ 2) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta color f := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss] using
    (realHilbertProjectionSweepStageResidualAmplitude_sq_sum_eq_pathLoss
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      ((Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
      f)

/-- Genuine spatial-link local profile: each link uses the sweep-stage profile
of its own canonical six-spatial color. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
    H N hN beta hbeta
    (periodicHypercubicEvenSpatialSliceLinkColor H e) f
    ⟨e, rfl⟩

/-- The genuine spatial-link local profile is pointwise nonnegative, as
required by the one-sided Schur receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_nonneg
      H N hN beta hbeta
      (periodicHypercubicEvenSpatialSliceLinkColor H e) f ⟨e, rfl⟩

/-- Reindexing all color fibers back to the genuine spatial-link carrier turns
the global squared local-profile energy into the sum of the six fixed-color
path losses. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_sq_sum_eq_colorPathLossSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2) =
      ∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color f := by
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2) =
        ∑ z :
            (Σ color : PeriodicHypercubicEvenGroundStateSpatialColor,
              PeriodicHypercubicEvenFixedSpatialColorLink H color),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
            H N hN beta hbeta z.1 f z.2 ^ 2 := by
      refine Fintype.sum_equiv
        (periodicHypercubicEvenSpatialSliceLinkEquivSigmaFixedSpatialColor H)
        _ _ ?_
      intro e
      rfl
    _ =
        ∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
          ∑ e : PeriodicHypercubicEvenFixedSpatialColorLink H color,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
              H N hN beta hbeta color f e ^ 2 := by
      simpa using
        (Fintype.sum_sigma'
          (fun color : PeriodicHypercubicEvenGroundStateSpatialColor =>
            fun e : PeriodicHypercubicEvenFixedSpatialColorLink H color =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile
                H N hN beta hbeta color f e ^ 2))
    _ =
        ∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta color f := by
      apply Finset.sum_congr rfl
      intro color _hcolor
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
          H N hN beta hbeta color f

/-- Exact receiver normalization: the normalized squared local-profile energy
is exactly the six-color one-link sweep path loss from the preceding theorem
unit. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (1 / 6 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e ^ 2 =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  have hColorReindex :
      (∑ color : PeriodicHypercubicEvenGroundStateSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta color f) =
        ∑ c : Fin 6,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f := by
    refine Fintype.sum_equiv
      periodicHypercubicEvenGroundStateSpatialColorEquivFin
      _ _ ?_
    intro color
    simp
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_sq_sum_eq_colorPathLossSum
      H N hN beta hbeta f,
    hColorReindex]
  rfl

/-- Main local-energy bridge: the normalized squared sweep-stage one-link
profile is charged to the genuine six-spatial residual energy with coefficient
one and no volume-dependent multiplicity factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_le_residualEnergy
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (1 / 6 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f e ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
      H N hN beta hbeta f]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss_le_residualEnergy
      H N hN beta hbeta f

end

end MGAP4D.MathlibAnalytic
