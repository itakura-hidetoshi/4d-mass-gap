import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedDefectSmallness

open MGAP4D.MathlibAnalytic
open MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

#check fixedColor_defect_le_lossRatio_mul_colorResidual_of_core
#check fixedColor_defect_le_lossRatio_mul_colorResidual
#check sixSpatial_defectMean_le_lossRatio_mul_residualEnergy
#check sixSpatial_residualEnergy_le_norm_sq
#check sixSpatial_defectMean_le_lossRatio_mul_norm_sq
#check sixSpatial_pathLoss_ge_one_sub_lossRatio_mul_residualEnergy
#check exists_jointLeakageLossRatioSmallnessCutoff
#check jointLeakageDefectMarginCutoff_pos
#check jointLeakageLossRatio_nonneg_lt_one_sixth
#check sixSpatial_defectMean_uniform_small

-- The final estimate is on arbitrary joint L2, with NO bounded-core premise.
example (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
      H N hN beta hbeta f ≤ jointLeakageLossRatio s beta * ‖f‖ ^ 2 := by
  exact sixSpatial_defectMean_le_lossRatio_mul_norm_sq H N hN beta hbeta s hs hcut f

-- Small sweep/block difference alone does not give a strict sector contraction.
example : (∀ x : ℝ, ‖(ContinuousLinearMap.id ℝ ℝ) x - (ContinuousLinearMap.id ℝ ℝ) x‖ ^ 2 = 0) ∧
    ¬ (∀ x : ℝ, ‖(ContinuousLinearMap.id ℝ ℝ) x‖ ^ 2 ≤ (5 / 6 : ℝ) * ‖x‖ ^ 2) := by
  constructor
  · intro x
    simp
  · intro h
    have hOne := h 1
    norm_num at hOne

-- A single cutoff and coefficient precede all volume/rank/vector choices.
example (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageDefectMarginCutoff s hs) :
    ∃ delta : ℝ, 0 ≤ delta ∧ delta < 1 / 6 ∧
      ∀ (H N : ℕ) (hN : 0 < N)
        (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN beta hbeta f ≤ delta * ‖f‖ ^ 2 := by
  exact ⟨jointLeakageLossRatio s beta, sixSpatial_defectMean_uniform_small s hs beta hbeta hcut⟩

-- Zero coupling on ALL joint L2, using a consistent explicit proof index.
example (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 le_rfl) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
      H N hN 0 le_rfl f = 0 := by
  have h := sixSpatial_defectMean_le_lossRatio_mul_norm_sq H N hN 0 le_rfl s hs
    (jointLeakageLossContractionCutoff_pos s hs).le f
  exact le_antisymm (by simpa using h)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq_nonneg
      H N hN 0 le_rfl f)

#print axioms fixedColor_defect_le_lossRatio_mul_colorResidual_of_core
#print axioms fixedColor_defect_le_lossRatio_mul_colorResidual
#print axioms sixSpatial_defectMean_le_lossRatio_mul_residualEnergy
#print axioms sixSpatial_defectMean_le_lossRatio_mul_norm_sq
#print axioms sixSpatial_pathLoss_ge_one_sub_lossRatio_mul_residualEnergy
#print axioms exists_jointLeakageLossRatioSmallnessCutoff
#print axioms sixSpatial_defectMean_uniform_small
