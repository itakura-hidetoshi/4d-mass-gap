import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialOrderedRelativeFrame

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
open scoped BigOperators

noncomputable section

#check allLinkSweep_leftVariance_le_lossRatio_mul
#check sixSpatialGroupedLinkList_nodup
#check sixSpatialGroupedLinkList_complete
#check fixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
#check sixSpatial_ordered_relativePoincare

-- Full genuine joint L2 and the existing cutoff: no additional comparison input.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    ((1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36) *
      ‖f - allRightLeftRetainedCondExpL2 H N hN beta hbeta f‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
          H N hN beta hbeta f := by
  exact sixSpatial_ordered_relativePoincare H N hN beta hbeta s hs hcut f

-- Positivity of the normalized six-color coefficient, independent of H and N.
example (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs) :
    0 < (1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36 := by
  have hQ := (jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut).2
  exact div_pos (sq_pos_of_pos (by linarith)) (by norm_num)

-- The new conservative bound at beta zero is 1/36, not the exact old 1/6.
example (s : ℝ) : (1 - 2 * jointLeakageSchurCoefficient s 0) ^ 2 / 36 = (1 / 36 : ℝ) := by
  simp

-- Relative control does not discard a retained component or imply an uncentered gap.
example : (∀ x : ℝ, ‖x - (ContinuousLinearMap.id ℝ ℝ) x‖ ^ 2 = 0) ∧
    ¬ (∀ x : ℝ, (1 / 36 : ℝ) * ‖x‖ ^ 2 ≤ ‖x - (ContinuousLinearMap.id ℝ ℝ) x‖ ^ 2) := by
  constructor
  · intro x; simp
  · intro h; have hOne := h 1; norm_num at hOne

-- Grouping preserves any order, including repeated groups; no projections assumed.
example {E I C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : I → E →L[ℝ] E) (groups : C → List I) (cs : List C) (x : E) :
    realHilbertProjectionSweep P (cs.flatMap groups) x =
      realHilbertProjectionSweep (fun c => realHilbertProjectionSweep P (groups c)) cs x :=
  GroupedProjectionSweep.flatMap_apply P groups cs x

-- One coefficient/cutoff precedes all volume/rank/observable choices.
example (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs) :
    ∀ (H N : ℕ) (hN : 0 < N)
      (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      ((1 - 2 * jointLeakageSchurCoefficient s beta) ^ 2 / 36) *
        ‖f - allRightLeftRetainedCondExpL2 H N hN beta hbeta f‖ ^ 2 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
            H N hN beta hbeta f := by
  intro H N hN f
  exact sixSpatial_ordered_relativePoincare H N hN beta hbeta s hs hcut f

#print axioms GroupedProjectionSweep.flatMap_apply
#print axioms GroupedProjectionSweep.displacement_le_sum_initial
#print axioms sixSpatialGroupedLinkList_nodup
#print axioms allLinkSweep_leftVariance_le_lossRatio_mul
#print axioms fixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
#print axioms sixSpatial_ordered_relativePoincare

end
