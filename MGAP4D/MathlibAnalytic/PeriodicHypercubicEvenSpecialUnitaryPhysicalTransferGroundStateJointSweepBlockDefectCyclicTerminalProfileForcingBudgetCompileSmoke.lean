import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectCyclicTerminalProfileForcingBudget

namespace MGAP4D.MathlibAnalytic

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicForcingBudget

#check
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicCommutatorForcingBudget

-- Regress the signed-vector-to-norm bridge under the entire physical import graph.
-- Only norm_neg may simplify it; no global beta-zero feedback simp rule is used.
example {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (target : C) (sources : List C) (x : E)
    (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ =
      ‖realHilbertProjectionSweepTargetCrossResidualVectorSum P target sources x‖ := by
  simpa only [norm_neg] using
    (congrArg (fun z : E => ‖z‖)
      (realHilbertProjectionSweep_targetResidual_eq_neg_crossResidualVectorSum_of_fixed
        P target sources x hFixed))

-- The fixed-start receiver consumes the original one-step hypothesis unchanged.
example {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (target : C) (forcing : C → E → ℝ)
    (hStep : ∀ (source : C) (x : E),
      ‖P source x - P target (P source x)‖ ≤
        forcing source x + ‖x - P target x‖)
    (sources : List C) (x : E) (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x :=
  realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed
    P target forcing hStep sources x hFixed

end MGAP4D.MathlibAnalytic
