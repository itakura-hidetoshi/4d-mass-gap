import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTargetCrossResidualTelescoping
import Mathlib.Tactic

/-!
# Cyclic terminal profile from an arbitrary one-step forcing budget

Fix a canonical target split

  canonicalList = pre ++ target :: suffix.

After the first target projection, the exact between-visits source order is

  suffix ++ pre.

The initial post-target vector is target-fixed.  Therefore the generic
target-residual forcing-budget telescope applies with zero initial residual.
Using the exact cyclic second-visit identification from #4913, this file turns
any one-step forcing estimate into a direct terminal-profile estimate.

The first theorem is deliberately forcing-agnostic.  The later analytic bridge
may instantiate the forcing by the existing pin-free response kernel times the
actual source-stage residual without changing this list argument.

A second theorem instantiates the generic result with the commutator forcing
budget from #4917--#4920.

No source reordering, finite-cardinality Cauchy estimate, arbitrary factor two,
or positive-beta commutativity is used.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

local instance cyclicTerminalProfileForcingBudgetSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Any one-step target-residual forcing estimate along the genuine fixed-color
one-link family controls the terminal profile by the forcing accumulated along
the exact cyclic between-visits trajectory. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hSplit : (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      pre ++ target :: suffix)
    (forcing : PeriodicHypercubicEvenFixedSpatialColorLink H color →
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta → ℝ)
    (hStep : ∀ (source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
      (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color source x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color source x)‖ ≤
        forcing source x +
          ‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target x‖) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color) forcing (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
      H N hN beta hbeta color pre f
  let x0 := P target y
  have hIdem :
      (P target).comp (P target) = P target := by
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta target.1
  have hFixed : P target x0 = x0 := by
    have h :=
      congrArg
        (fun T :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta =>
          T y)
        hIdem
    simpa [x0] using h
  have hBudget :=
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
      P target forcing
      (by
        intro source x
        simpa [P] using hStep source x)
      (suffix ++ pre) x0 hFixed
  have hTel :=
    realHilbertProjectionSweep_targetResidual_eq_neg_crossResidualVectorSum_of_fixed
      P target (suffix ++ pre) x0 hFixed
  have hProfile :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_eq_norm_targetCrossResidualVectorSum
      H N hN beta hbeta color pre suffix target f hSplit
  have hNorm :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f target =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ := by
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f target =
        ‖realHilbertProjectionSweepTargetCrossResidualVectorSum
            P target (suffix ++ pre) x0‖ := by
              simpa [P, y, x0] using hProfile
      _ =
        ‖-realHilbertProjectionSweepTargetCrossResidualVectorSum
            P target (suffix ++ pre) x0‖ := by
              simp
      _ =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ := by
              rw [hTel]
  rw [hNorm]
  simpa [P, y, x0] using hBudget

/-- The same cyclic terminal-profile bound with the canonical commutator
forcing budget. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicCommutatorForcingBudget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ target :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        target
        (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
      H N hN beta hbeta color pre f
  let x0 := P target y
  have hIdem : ∀ e, (P e).comp (P e) = P e := by
    intro e
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e.1
  have hSymm :
      ∀
        (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
        (u v :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta),
        inner ℝ (P e u) v = inner ℝ u (P e v) := by
    intro e u v
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e.1 u v
  have hFixed : P target x0 = x0 := by
    have h :=
      congrArg
        (fun T :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta →L[ℝ]
            PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
              H N hN beta hbeta =>
          T y)
        (hIdem target)
    simpa [x0] using h
  have hBudget :=
    realHilbertProjectionSweep_targetResidual_norm_le_commutatorForcingBudget_of_fixed
      P target hIdem hSymm (suffix ++ pre) x0 hFixed
  have hTel :=
    realHilbertProjectionSweep_targetResidual_eq_neg_crossResidualVectorSum_of_fixed
      P target (suffix ++ pre) x0 hFixed
  have hProfile :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_eq_norm_targetCrossResidualVectorSum
      H N hN beta hbeta color pre suffix target f hSplit
  have hNorm :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f target =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ := by
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
          H N hN beta hbeta color f target =
        ‖realHilbertProjectionSweepTargetCrossResidualVectorSum
            P target (suffix ++ pre) x0‖ := by
              simpa [P, y, x0] using hProfile
      _ =
        ‖-realHilbertProjectionSweepTargetCrossResidualVectorSum
            P target (suffix ++ pre) x0‖ := by
              simp
      _ =
        ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ := by
              rw [hTel]
  rw [hNorm]
  simpa [P, y, x0] using hBudget

end

end MGAP4D.MathlibAnalytic
