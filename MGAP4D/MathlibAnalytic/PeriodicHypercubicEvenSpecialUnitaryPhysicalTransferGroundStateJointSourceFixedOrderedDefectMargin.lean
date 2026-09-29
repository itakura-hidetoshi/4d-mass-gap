import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedRenewalContraction

/-!
# Ordered sweep/block defect control on the full genuine joint L2 carrier

Combine the actual loss estimate with the actual strict renewal contraction:
  D_c(f) = L_c(S_c f) + D_c(S_c f)
         <= eta * (L_c(f) + D_c(f))
          = eta * ||f - B_c f||^2.
The bounded concrete core is already dense. Both quadratic forms are
continuous, so this precise relative inequality extends to all joint L2.
Averaging with the existing 1/6 gives Dmean <= eta E6 <= eta ||f||^2,
and the exact split E6 = L + Dmean gives (1-eta) E6 <= L.

No density statement about an intersection with the physical sector is needed.
No pointwise representative of an arbitrary L2 class is chosen. The coefficient
is the SAME ordered eta from #4938/#4939; no volume factor or extra division
by 1-eta is introduced. This is not a positive-beta sector contraction or gap.
-/

namespace MGAP4D.MathlibAnalytic

open Set
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

namespace GroundStateSourceFixedPairEnergy

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "Core" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta
local notation "S" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector H N hN beta hbeta
local notation "B" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialColorCondExpL2 H N hN beta hbeta
local notation "L" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss H N hN beta hbeta
local notation "DV" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector H N hN beta hbeta
local notation "Dmean" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq H N hN beta hbeta
local notation "E6" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy H N hN beta hbeta
local notation "L6" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss H N hN beta hbeta

/-- The exact relative defect coefficient on the original analytic core. -/
theorem fixedColor_defect_le_lossRatio_mul_colorResidual_of_core
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (hf : f ∈ Core) :
    ‖DV color f‖ ^ 2 ≤ jointLeakageLossRatio s beta * ‖f - B color f‖ ^ 2 := by
  have hLoss := fixedColor_terminalPathLoss_le_lossRatio_mul
    H N hN beta hbeta s hs hcut color f hf
  have hNext := fixedColor_nextDefect_le_lossRatio_mul
    H N hN beta hbeta s hs hcut color f hf
  have hRenew :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefect_norm_sq_eq_terminalSweepPathLoss_add_nextDefect_norm_sq
      H N hN beta hbeta color f
  have hSplit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColor_residual_norm_sq_eq_sweepPathLoss_add_sweepBlockDefect_norm_sq
      H N hN beta hbeta color f
  rw [hSplit]
  nlinarith

/-- Extend the SAME relative quadratic inequality by the existing core density.
There is no core premise on the final joint-L2 input. -/
theorem fixedColor_defect_le_lossRatio_mul_colorResidual
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) :
    ‖DV color f‖ ^ 2 ≤ jointLeakageLossRatio s beta * ‖f - B color f‖ ^ 2 := by
  let good : Set JL2 := {g | ‖DV color g‖ ^ 2 ≤
    jointLeakageLossRatio s beta * ‖g - B color g‖ ^ 2}
  have hLeft : Continuous (fun g : JL2 => ‖DV color g‖ ^ 2) := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepBlockDefectVector
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
    fun_prop
  have hRight : Continuous (fun g : JL2 =>
      jointLeakageLossRatio s beta * ‖g - B color g‖ ^ 2) := by fun_prop
  have hClosed : IsClosed good := isClosed_le hLeft hRight
  have hCoreSub : Core ⊆ good := by
    intro g hg
    exact fixedColor_defect_le_lossRatio_mul_colorResidual_of_core
      H N hN beta hbeta s hs hcut color g hg
  have hClosureSub : closure Core ⊆ good := closure_minimal hCoreSub hClosed
  have hDense : Dense Core :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
      H N hN beta hbeta
  exact hClosureSub (by rw [hDense.closure_eq]; exact Set.mem_univ f)

private theorem sixSpatial_residualEnergy_eq_colorAverage (f : JL2) :
    E6 f = (1 / 6 : ℝ) * ∑ c : Fin 6,
      ‖f - B (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 := by
  simp only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy,
    groundStateJointColorNormalizedResidualEnergy,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2,
    Fintype.card_fin, one_div]
  norm_num

/-- The exact normalized six-color relative estimate, now on all joint L2. -/
theorem sixSpatial_defectMean_le_lossRatio_mul_residualEnergy
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) : Dmean f ≤ jointLeakageLossRatio s beta * E6 f := by
  have hSum :
      (∑ c : Fin 6, ‖DV (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2) ≤
        ∑ c : Fin 6, jointLeakageLossRatio s beta *
          ‖f - B (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 :=
    Finset.sum_le_sum fun c _ => fixedColor_defect_le_lossRatio_mul_colorResidual
      H N hN beta hbeta s hs hcut (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
  calc
    _ ≤ (1 / 6 : ℝ) * ∑ c : Fin 6, jointLeakageLossRatio s beta *
        ‖f - B (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hSum (by norm_num)
    _ = jointLeakageLossRatio s beta * E6 f := by
      rw [sixSpatial_residualEnergy_eq_colorAverage H N hN beta hbeta f, ← Finset.mul_sum]
      ring

/-- Orthogonal projections give the ambient energy upper bound at every beta.
This is an upper bound, not physical-sector coercivity. -/
theorem sixSpatial_residualEnergy_le_norm_sq (f : JL2) : E6 f ≤ ‖f‖ ^ 2 := by
  let P6 := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
    H N hN beta hbeta
  change groundStateJointColorNormalizedResidualEnergy P6 f ≤ ‖f‖ ^ 2
  rw [groundStateJointColorNormalizedResidualEnergy_eq_norm_sq_sub_meanProjectedNormSq
    P6
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_idempotent
      H N hN beta hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2_symmetric
      H N hN beta hbeta)]
  exact sub_le_self _ (by unfold groundStateJointColorMeanProjectedNormSq; positivity)

/-- The uniform absolute defect coefficient is eta itself, without a further
factor 1/(1-eta). The argument is any genuine joint-L2 vector. -/
theorem sixSpatial_defectMean_le_lossRatio_mul_norm_sq
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) : Dmean f ≤ jointLeakageLossRatio s beta * ‖f‖ ^ 2 :=
  (sixSpatial_defectMean_le_lossRatio_mul_residualEnergy H N hN beta hbeta s hs hcut f).trans
    (mul_le_mul_of_nonneg_left (sixSpatial_residualEnergy_le_norm_sq H N hN beta hbeta f)
      (jointLeakageLossRatio_nonneg s beta))

/-- Equivalent path-loss coercivity RELATIVE to the six-color residual energy.
No lower bound on that energy on a physical sector is asserted. -/
theorem sixSpatial_pathLoss_ge_one_sub_lossRatio_mul_residualEnergy
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : JL2) : (1 - jointLeakageLossRatio s beta) * E6 f ≤ L6 f := by
  have hDefect := sixSpatial_defectMean_le_lossRatio_mul_residualEnergy
    H N hN beta hbeta s hs hcut f
  have hSplit :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy_eq_sweepPathLoss_add_sweepBlockDefectMeanNormSq
      H N hN beta hbeta f
  nlinarith

end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
