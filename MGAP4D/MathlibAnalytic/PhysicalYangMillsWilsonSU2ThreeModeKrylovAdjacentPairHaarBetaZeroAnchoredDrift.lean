import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFrozenZeroAllLinkVanishing
import Mathlib.Tactic

/-!
# P4: true positive-beta posterior residuals anchored at the exact beta-zero endpoint

The original frozen-beta-zero posterior projection fixes every genuine
physical pair-Haar receiver (#5279). At any nonnegative frozen beta,
the ORIGINAL transported posterior residual therefore splits exactly
into two defects in the SAME pair-Haar L2 carrier:

1. physical receiver drift V_beta f - V_0 f, acted on by I - Q_beta,e;
2. original posterior-projection drift (Q_0,e - Q_beta,e) V_0 f.

The resulting full-link squared residual is at most twice the sum of
these two full-link squared defects. No spatial link-count factor is
introduced. This reduction makes both remaining genuine perturbative
estimates explicit; it does NOT prove either is uniformly bounded in
volume for positive beta.

Original joint law, true half-density conjugation, signed normalized
receiver, beta distinction, and physical transfer remain unchanged.
No Dobrushin or new posterior kernel, and no continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p4AnchoredTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4AnchoredCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4AnchoredSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4AnchoredMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4AnchoredBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4AnchoredSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Squared triangle estimate, proved without an unnecessary link count. -/
private theorem norm_add_sq_le_two_norm_sq
    {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have htri : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have hleft : 0 ≤ ‖x + y‖ := norm_nonneg _
  have hright : 0 ≤ ‖x‖ + ‖y‖ :=
    add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hprod :
      0 ≤ (‖x‖ + ‖y‖ - ‖x + y‖) * (‖x‖ + ‖y‖ + ‖x + y‖) :=
    mul_nonneg (sub_nonneg.mpr htri) (add_nonneg hright hleft)
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

/-- Exact original positive-beta posterior defect equals the change of
the true physical receiver plus the change of the true transported
posterior projection, anchored at Q_0 V_0 f = V_0 f from #5279. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_linkResidual_eq_zeroAnchored
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f) =
      ((normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
          normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
            normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)) +
      (pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)) := by
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let v₀ := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
  let Q₀ := pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
  have hzero : Q₀ v₀ = v₀ :=
    normalizedPhysicalOneSlabPairHaarReceiver_zero_spatialLink_fixed H N hN f e
  have hQsub : Q (v - v₀) = Q v - Q v₀ := by
    simp only [Q, pairHaarTransportedGroundStateSpatialLinkProjection, map_sub]
  change v - Q v = (v - v₀ - Q (v - v₀)) + (Q₀ v₀ - Q v₀)
  rw [hzero, hQsub]
  abel

/-- Pointwise positive-beta defect is bounded by two TRUE drifts, rather
than by a link-count times an L2 bound. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_linkResidual_sq_le_zeroAnchored
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
      pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
        (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2 ≤
      2 * (‖(normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
          normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
            normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2 +
      ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) := by
  rw [normalizedPhysicalOneSlabPairHaarReceiver_beta_linkResidual_eq_zeroAnchored
    H N hN beta hbeta f e]
  exact norm_add_sq_le_two_norm_sq _ _

/-- Genuine FULL spatial-link squared loss at positive frozen beta:
a no-link-count reduction to the actual physical receiver and posterior
projection drifts from the exact beta-zero endpoint. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_beta_fullLinkResidual_le_zeroAnchored
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
        pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
          (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f)‖ ^ 2) ≤
      2 * ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
            normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f -
              normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2) +
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f)‖ ^ 2)) := by
  classical
  let v := normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f
  let v₀ := normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) f
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta
  let Q₀ := pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num)
  change (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
    ‖v - Q e v‖ ^ 2) ≤
    2 * ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      ‖(v - v₀) - Q e (v - v₀)‖ ^ 2) +
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖Q₀ e v₀ - Q e v₀‖ ^ 2))
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v - Q e v‖ ^ 2) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          2 * (‖(v - v₀) - Q e (v - v₀)‖ ^ 2 +
            ‖Q₀ e v₀ - Q e v₀‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro e _he
      exact normalizedPhysicalOneSlabPairHaarReceiver_beta_linkResidual_sq_le_zeroAnchored
        H N hN beta hbeta f e
    _ = 2 * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (‖(v - v₀) - Q e (v - v₀)‖ ^ 2 +
          ‖Q₀ e v₀ - Q e v₀‖ ^ 2)) := by
      rw [Finset.mul_sum]
    _ = 2 * ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖(v - v₀) - Q e (v - v₀)‖ ^ 2) +
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖Q₀ e v₀ - Q e v₀‖ ^ 2)) := by
      rw [Finset.sum_add_distrib]

/-- The ACTUAL physical-family residual Gram diagonal inherits the
same original two-drift criterion. A bound on its two true full-link
terms yields a Rayleigh bound by #5273, without counting links. -/
theorem pairHaarSpatialLinkResidualGram_physicalFamily_diag_le_zeroAnchored
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    {ι : Type*} [Fintype ι]
    (f : ι → periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (i : ι) :
    pairHaarSpatialLinkResidualGram H N hN beta hbeta
      (fun j => normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f j)) i i ≤
      2 * ((∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖(normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i) -
            normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta (f i) -
              normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i))‖ ^ 2) +
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖pairHaarTransportedGroundStateSpatialLinkProjection H N hN 0 (by norm_num) e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i)) -
          pairHaarTransportedGroundStateSpatialLinkProjection H N hN beta hbeta e
            (normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) (f i))‖ ^ 2)) := by
  rw [pairHaarSpatialLinkResidualGram_diag]
  exact normalizedPhysicalOneSlabPairHaarReceiver_beta_fullLinkResidual_le_zeroAnchored
    H N hN beta hbeta (f i)

end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
