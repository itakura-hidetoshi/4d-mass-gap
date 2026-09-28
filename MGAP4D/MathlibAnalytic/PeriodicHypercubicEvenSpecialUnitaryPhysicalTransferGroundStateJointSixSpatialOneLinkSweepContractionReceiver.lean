import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOneLinkSweepPathLoss
import Mathlib.Tactic

/-!
# Six-spatial one-link sweep contraction receiver

The previous direct-update route exposes a structural normalization obstruction:
summing off-diagonal target differences first is not the right volume-uniform
quantity.  The canonical same-color one-link sweep already provides the
correct fixed-six-color carrier.

For one spatial color, orthogonal-projection Pythagoras gives exactly

  pathLoss_color(f)
    = ||f||^2 - ||fullSweep_color(f)||^2.

Averaging over the six spatial colors therefore gives

  sixSpatialOneLinkSweepPathLoss(f)
    = ||f||^2 - meanColor ||fullSweep_color(f)||^2.

Consequently any strict contraction

  meanColor ||fullSweep_color(f)||^2 <= q ||f||^2

immediately yields

  (1-q) ||f||^2
    <= sixSpatialOneLinkSweepPathLoss(f)
    <= sixSpatialResidualEnergy(f).

This is the volume-free receiver for the positive-beta analysis.  It keeps the
exact six-color normalization and does not introduce a target/source
cardinality factor, Cauchy loss, factor two, or commutativity assumption among
positive-beta one-link projections.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

local instance sixSpatialOneLinkSweepContractionReceiverSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Terminal vector after sweeping every one-link conditional expectation in
one fixed spatial color exactly once, in the canonical order. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  realHilbertProjectionSweep
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color)
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
    f

/-- Exact fixed-color norm-loss identity for the complete canonical one-link
sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss_eq_norm_sq_sub_fullSweep_norm_sq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
        H N hN beta hbeta color f =
      ‖f‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f‖ ^ 2 := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let cs :=
    ((Finset.univ :
      Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList)
  have hLoss :=
    realHilbertProjectionSweep_norm_sq_loss
      P
      (fun e => by
        simpa [P,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
            H N hN beta hbeta e.1)
      (fun e x y =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
          H N hN beta hbeta e.1 x y)
      cs f
  simpa [
    P, cs,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector] using
    hLoss.symm

/-- Mean squared terminal norm of the six complete same-color one-link sweeps. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) : ℝ :=
  (1 / 6 : ℝ) *
    ∑ c : Fin 6,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2

/-- Exact six-color identity: the normalized one-link sweep path loss is the
initial squared norm minus the mean squared terminal norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss_eq_norm_sq_sub_fullSweepMeanNormSq
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f =
      ‖f‖ ^ 2 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
          H N hN beta hbeta f := by
  let T :=
    fun c : Fin 6 =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  have hEach :
      ∀ c : Fin 6,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
            H N hN beta hbeta
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f =
          ‖f‖ ^ 2 - ‖T c‖ ^ 2 := by
    intro c
    simpa [T] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss_eq_norm_sq_sub_fullSweep_norm_sq
        H N hN beta hbeta
        (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  have hSum :
      (∑ c : Fin 6,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f) =
        (6 : ℝ) * ‖f‖ ^ 2 - ∑ c : Fin 6, ‖T c‖ ^ 2 := by
    calc
      (∑ c : Fin 6,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss
          H N hN beta hbeta
          (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f) =
          ∑ c : Fin 6, (‖f‖ ^ 2 - ‖T c‖ ^ 2) := by
            apply Finset.sum_congr rfl
            intro c _hc
            exact hEach c
      _ = (∑ _c : Fin 6, ‖f‖ ^ 2) -
          ∑ c : Fin 6, ‖T c‖ ^ 2 := by
            rw [Finset.sum_sub_distrib]
      _ = (6 : ℝ) * ‖f‖ ^ 2 -
          ∑ c : Fin 6, ‖T c‖ ^ 2 := by
            simp
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
  rw [hSum]
  dsimp [T]
  ring

/-- A contraction of the six-color mean terminal norm yields a volume-free
lower bound on the genuine six-spatial residual energy with the complementary
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq_le_implies_residualEnergy_lower
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (q : ℝ)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hcontract :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkFullSweepMeanNormSq
          H N hN beta hbeta f ≤
        q * ‖f‖ ^ 2) :
    (1 - q) * ‖f‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f := by
  have hPathEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss_eq_norm_sq_sub_fullSweepMeanNormSq
      H N hN beta hbeta f
  have hLower :
      (1 - q) * ‖f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f := by
    rw [hPathEq]
    nlinarith
  exact
    hLower.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss_le_residualEnergy
        H N hN beta hbeta f)

end

end MGAP4D.MathlibAnalytic
