import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedDefectMargin

/-!
# Arbitrarily small volume-uniform ordered defect coefficients

Use the elementary real formula for the SAME ordered Q near zero. Its ratio
(Q/(1-Q))^2 is continuous at zero and vanishes there. For any positive epsilon,
choose a positive cutoff nested inside the existing loss-contraction cutoff
on which eta < epsilon. Specializing epsilon=1/6 gives an actual full-joint-L2
defect bound with delta=eta<1/6, uniform in volume and rank.

No maximal numerical beta is computed. No beta-zero 5/6 sector coefficient is
transported to positive beta, and the positive-beta physical gap is not asserted.
-/

namespace MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy

open scoped BigOperators

noncomputable section

/-- Arbitrary positive tolerance, with no volume, rank or observable argument. -/
theorem exists_jointLeakageLossRatioSmallnessCutoff
    (s : ℝ) (hs : 8 < s) (epsilon : ℝ) (hEpsilon : 0 < epsilon) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ jointLeakageLossContractionCutoff s hs ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ cutoff → jointLeakageLossRatio s beta < epsilon := by
  let qReal : ℝ → ℝ := fun beta =>
    jointLeakageRMSMultiplierRealFormula s beta *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient s beta
  let etaReal : ℝ → ℝ := fun beta => (qReal beta / (1 - qReal beta)) ^ 2
  have hQContinuous : ContinuousAt qReal 0 :=
    (continuousAt_jointLeakageRMSMultiplierRealFormula s).mul
      (continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient s)
  have hQZero : qReal 0 = 0 := by simp [qReal]
  have hDenZero : 1 - qReal 0 ≠ 0 := by rw [hQZero]; norm_num
  have hContinuous : ContinuousAt etaReal 0 :=
    (hQContinuous.div (continuousAt_const.sub hQContinuous) hDenZero).pow 2
  have hEtaZero : etaReal 0 = 0 := by simp [etaReal, hQZero]
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ := hContinuous epsilon hEpsilon
  let cutoff := min (delta / 2) (jointLeakageLossContractionCutoff s hs)
  have hPos : 0 < cutoff :=
    lt_min (by positivity) (jointLeakageLossContractionCutoff_pos s hs)
  have hCut : cutoff ≤ jointLeakageLossContractionCutoff s hs := min_le_right _ _
  refine ⟨cutoff, hPos, hCut, ?_⟩
  intro beta hbeta hbetaCut
  have hHalf : beta ≤ delta / 2 := hbetaCut.trans (min_le_left _ _)
  have hDistance : dist beta 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbeta]
    linarith
  have hAbs : |etaReal beta - etaReal 0| < epsilon := by
    simpa only [Real.dist_eq] using hControl hDistance
  have hUpper : etaReal beta - etaReal 0 < epsilon :=
    lt_of_le_of_lt (le_abs_self _) hAbs
  rw [hEtaZero, sub_zero] at hUpper
  have hStrict := ((hbetaCut.trans hCut).trans
    (jointLeakageLossContractionCutoff_le_schurCutoff s hs)).trans
      (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  have hQIdentify : jointLeakageSchurCoefficient s beta = qReal beta := by
    dsimp [jointLeakageSchurCoefficient, qReal]
    rw [jointLeakageRMSMultiplier_eq_realFormula s beta hbeta hStrict]
  simpa only [jointLeakageLossRatio, hQIdentify, etaReal] using hUpper

/-- Positive cutoff for the exact eta defect coefficient to be below 1/6. -/
def jointLeakageDefectMarginCutoff (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose (exists_jointLeakageLossRatioSmallnessCutoff s hs (1 / 6) (by norm_num))

theorem jointLeakageDefectMarginCutoff_pos (s : ℝ) (hs : 8 < s) :
    0 < jointLeakageDefectMarginCutoff s hs :=
  (Classical.choose_spec (exists_jointLeakageLossRatioSmallnessCutoff s hs (1 / 6) (by norm_num))).1

theorem jointLeakageDefectMarginCutoff_le_lossContractionCutoff (s : ℝ) (hs : 8 < s) :
    jointLeakageDefectMarginCutoff s hs ≤ jointLeakageLossContractionCutoff s hs :=
  (Classical.choose_spec (exists_jointLeakageLossRatioSmallnessCutoff s hs (1 / 6) (by norm_num))).2.1

theorem jointLeakageLossRatio_nonneg_lt_one_sixth
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageDefectMarginCutoff s hs) :
    0 ≤ jointLeakageLossRatio s beta ∧ jointLeakageLossRatio s beta < 1 / 6 :=
  ⟨jointLeakageLossRatio_nonneg s beta,
    (Classical.choose_spec
      (exists_jointLeakageLossRatioSmallnessCutoff s hs (1 / 6) (by norm_num))).2.2 beta hbeta hcut⟩

/-- Uniform quantifier order: one delta=eta<1/6, then every volume/rank and
EVERY joint-L2 vector. There is no bounded-core or physical-sector premise. -/
theorem sixSpatial_defectMean_uniform_small
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageDefectMarginCutoff s hs) :
    0 ≤ jointLeakageLossRatio s beta ∧ jointLeakageLossRatio s beta < 1 / 6 ∧
      ∀ (H N : ℕ) (hN : 0 < N)
        (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepBlockDefectMeanNormSq
          H N hN beta hbeta f ≤ jointLeakageLossRatio s beta * ‖f‖ ^ 2 := by
  have hSmall := jointLeakageLossRatio_nonneg_lt_one_sixth s hs beta hbeta hcut
  refine ⟨hSmall.1, hSmall.2, ?_⟩
  intro H N hN f
  exact sixSpatial_defectMean_le_lossRatio_mul_norm_sq H N hN beta hbeta s hs
    (hcut.trans (jointLeakageDefectMarginCutoff_le_lossContractionCutoff s hs)) f

end
end MGAP4D.MathlibAnalytic.GroundStateSourceFixedPairEnergy
