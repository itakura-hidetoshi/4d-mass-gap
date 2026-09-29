import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTargetCrossResidualTelescoping
import Mathlib.Tactic

/-!
# Cyclic terminal profile from a one-step forcing budget

For canonicalList = pre ++ target :: suffix, the vector immediately after
its first target projection is target-fixed. Its exact between-visits order
is suffix ++ pre. The fixed-start forcing telescope therefore bounds the
terminal profile without an initial residual or a cardinality multiplier.

The signed vector telescope is transported to norms by congrArg and norm_neg,
not by expanding the physical L2 carrier or using the global simp set.
The commutator-budget theorem is a specialization of the general receiver.

This remains a receiver: a volume-uniform beta-small forcing estimate is not
assumed to follow merely from exact beta-zero vanishing. No source/target
reversal, response symmetry, or positive-beta commutativity is used.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

local instance cyclicTerminalProfileForcingBudgetSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

/-- A one-step forcing estimate controls the terminal profile along the exact
cyclic between-visits trajectory, with no initial target residual. -/
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
            H N hN beta hbeta color source x)‖ ≤ forcing source x +
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
  have hIdem : (P target).comp (P target) = P target := by
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta target.1
  have hFixed : P target x0 = x0 := by
    have h := congrArg
      (fun T :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta →L[ℝ]
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta => T y)
      hIdem
    simpa only [x0, ContinuousLinearMap.comp_apply] using h
  have hBudget :=
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
      P target forcing hStep (suffix ++ pre) x0 hFixed
  have hTel :=
    realHilbertProjectionSweep_targetResidual_eq_neg_crossResidualVectorSum_of_fixed
      P target (suffix ++ pre) x0 hFixed
  have hNorm :
      ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
          P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ =
        ‖realHilbertProjectionSweepTargetCrossResidualVectorSum P target (suffix ++ pre) x0‖ := by
    simpa only [norm_neg] using
      (congrArg
        (fun z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta => ‖z‖) hTel)
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target =
      ‖realHilbertProjectionSweepTargetCrossResidualVectorSum P target (suffix ++ pre) x0‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_eq_norm_targetCrossResidualVectorSum
        H N hN beta hbeta color pre suffix target f hSplit
    _ = ‖realHilbertProjectionSweep P (suffix ++ pre) x0 -
        P target (realHilbertProjectionSweep P (suffix ++ pre) x0)‖ := hNorm.symm
    _ ≤ realHilbertProjectionSweepTargetResidualForcingBudget
        P forcing (suffix ++ pre) x0 := hBudget

/-- The commutator forcing budget is an exact specialization of the preceding
receiver; its projected-input coefficient is not weakened to a full norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicCommutatorForcingBudget
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (target : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hSplit : (Finset.univ : Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
      pre ++ target :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta color f target ≤
      realHilbertProjectionSweepTargetResidualCommutatorForcingBudget
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color) target (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  have hIdem : ∀ e, (P e).comp (P e) = P e := by
    intro e
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e.1
  have hSymm : ∀ (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
      (u v : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      inner ℝ (P e u) v = inner ℝ u (P e v) := by
    intro e u v
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e.1 u v
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget
      H N hN beta hbeta color pre suffix target f hSplit
      (fun source x =>
        realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source * ‖P target x‖)
      (fun source x =>
        realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
          P target source hIdem hSymm x)

end

end MGAP4D.MathlibAnalytic
