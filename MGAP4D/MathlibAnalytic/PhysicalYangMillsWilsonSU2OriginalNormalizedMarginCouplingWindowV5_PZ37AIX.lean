import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSpatialMeanNormalizationV5_PZ37AIW

/-!
# P4-Q2-PZ37AIX — true physical norm normalization for volume-dependent couplings

This is an append-only extension of AIW's *original* physical-transfer
normalization. The finite-volume configuration, complete SU(2) Wilson action,
both endpoint halfweights, normalized Haar measure, centered signed ZW L²
source, original AIG strict negative region, and actual Gauss-law transfer
operator are unchanged.

AIW proves decay of the original normalized negative-margin certificate at
each fixed positive coupling. Here the coupling may depend on the volume H.
For any fixed a > 0 and finite b, EVERY schedule beta_H in [a,b] obeys

  0 < delta_H(beta_H) / ||P_H,beta_H||
    <= (b/8) * p_H^2 * exp(-a*p_H)  --> 0.

The convergence and eventual smallness are simultaneous over all couplings
in the closed window, not merely a pointwise collection of fixed-beta limits.
This is not asserted for an arbitrary volume-dependent coupling without a
positive lower and finite upper bound.

The actual existing normalized physical transfer has norm one, and the
normalized strict negative region equals the unchanged AIG region for every
allowed (H,beta). The honest all-boundary normalized-source envelope remains
potentially growing; no assertion of decay of actual normalized source images,
uniform half-Haar for varying beta, excitation gap, or continuum mass gap is
made. Original H-dependent Hilbert and configuration spaces are preserved.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

local notation "pAIX" => p4Q2PZ37AFZ_plaquetteCount
local notation "mAIX" => p4Q2PZ37AIW_originalNormalizedNegativeMargin
local notation "uAIX" => p4Q2PZ37AIW_originalNormalizedSourceTransfer
local notation "NAIX" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator

/-- An exact pointwise uniform envelope for the ORIGINAL AIG negative-margin
certificate under the EXISTING physical norm normalization. The window is
[a,b], with 0<a<=beta<=b. There is no volume-independent change of source,
measure, operator, region, or certificate. -/
theorem p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope
    (H : ℕ) (a b beta : ℝ) (ha : 0 < a)
    (hLow : a ≤ beta) (hHigh : beta ≤ b) :
    mAIX H beta (le_trans ha.le hLow) ≤
      (b / 8) * ((pAIX H) ^ 2 * Real.exp (-(a * pAIX H))) := by
  have hBeta : 0 ≤ beta := le_trans ha.le hLow
  have hp : 0 ≤ pAIX H := (p4Q2PZ37AHN_count_pos H).le
  have hExp : Real.exp (-(beta * pAIX H)) ≤
      Real.exp (-(a * pAIX H)) := by
    exact Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_right hLow hp))
  have hShape : (pAIX H) ^ 2 * Real.exp (-(beta * pAIX H)) ≤
      (pAIX H) ^ 2 * Real.exp (-(a * pAIX H)) :=
    mul_le_mul_of_nonneg_left hExp (sq_nonneg _)
  have hCoef : 0 ≤ beta / 8 := div_nonneg hBeta (by norm_num)
  have hCoefLe : beta / 8 ≤ b / 8 :=
    div_le_div_of_nonneg_right hHigh (by norm_num)
  have hShapeNonneg : 0 ≤
      (pAIX H) ^ 2 * Real.exp (-(a * pAIX H)) :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ (beta / 8) * ((pAIX H) ^ 2 * Real.exp (-(beta * pAIX H))) :=
      p4Q2PZ37AIW_originalNormalizedNegativeMargin_le_countEnvelope H beta hBeta
    _ ≤ (beta / 8) * ((pAIX H) ^ 2 * Real.exp (-(a * pAIX H))) :=
      mul_le_mul_of_nonneg_left hShape hCoef
    _ ≤ (b / 8) * ((pAIX H) ^ 2 * Real.exp (-(a * pAIX H))) :=
      mul_le_mul_of_nonneg_right hCoefLe hShapeNonneg

/-- The common upper envelope is asymptotically zero for every positive
window floor a and every fixed finite upper endpoint b. -/
theorem p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope_tendsto_zero
    (a b : ℝ) (ha : 0 < a) :
    Tendsto
      (fun H : ℕ => (b / 8) *
        ((pAIX H) ^ 2 * Real.exp (-(a * pAIX H))))
      atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (p4Q2PZ37AIT_originalCountSquareExp_tendsto_zero a ha).const_mul (b / 8)

/-- One volume cutoff works for every coupling in the same compact positive
window, for the actual norm-normalized original AIG certificate. -/
theorem p4Q2PZ37AIX_originalNormalizedMargin_window_eventually_small
    (a b eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H → ∀ beta : ℝ,
      (hLow : a ≤ beta) → (hHigh : beta ≤ b) →
        0 < mAIX H beta (le_trans ha.le hLow) ∧
          mAIX H beta (le_trans ha.le hLow) < eta := by
  have hEnv :=
    (p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope_tendsto_zero a b ha).eventually
      (gt_mem_nhds heta)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hEnv
  refine ⟨N, ?_⟩
  intro H hHN beta hLow hHigh
  constructor
  · exact p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta
      (lt_of_lt_of_le ha hLow)
  · exact lt_of_le_of_lt
      (p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope H a b beta ha hLow hHigh)
      (hN H hHN)

/-- This is a genuine volume-dependent coupling statement: the original
certificate tends to zero along EVERY schedule beta_H confined to [a,b].
The Hilbert space varies with H and no common operator limit is postulated. -/
theorem p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_tendsto_zero
    (beta : ℕ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hLow : ∀ H : ℕ, a ≤ beta H)
    (hHigh : ∀ H : ℕ, beta H ≤ b) :
    Tendsto
      (fun H : ℕ =>
        mAIX H (beta H) (le_trans ha.le (hLow H)))
      atTop (𝓝 0) := by
  have hEnv :=
    p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope_tendsto_zero a b ha
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hEnv
    (fun H => (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H (beta H)
      (lt_of_lt_of_le ha (hLow H))).le)
    (fun H => p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope
      H a b (beta H) ha (hLow H) (hHigh H))

/-- A uniform positive floor for this very certificate is impossible along
any schedule in the fixed compact positive coupling window. This concerns the
certificate ONLY, not a different margin or a normalized spectral gap. -/
theorem p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_noPositiveFloor
    (beta : ℕ → ℝ) (a b : ℝ) (ha : 0 < a)
    (hLow : ∀ H : ℕ, a ≤ beta H)
    (hHigh : ∀ H : ℕ, beta H ≤ b) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ H : ℕ, c ≤ mAIX H (beta H) (le_trans ha.le (hLow H)) := by
  rintro ⟨c, hc, hFloor⟩
  have hEvent :=
    (p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_tendsto_zero
      beta a b ha hLow hHigh).eventually (gt_mem_nhds hc)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hEvent
  exact (not_lt_of_ge (hFloor N)) (hN N le_rfl)

/-- The original norm-one normalized operator and exact original AIG negative
set persist at the SAME cutoff as the window-uniform small positive
certificate. We do not assert a uniform half-Haar bound for varying beta. -/
theorem p4Q2PZ37AIX_originalNormalizedMargin_window_with_physicalOperator
    (a b eta : ℝ) (ha : 0 < a) (heta : 0 < eta) :
    ∃ N : ℕ, ∀ H : ℕ, N ≤ H → ∀ beta : ℝ,
      (hLow : a ≤ beta) → (hHigh : beta ≤ b) →
        0 < mAIX H beta (le_trans ha.le hLow) ∧
        mAIX H beta (le_trans ha.le hLow) < eta ∧
        ‖NAIX H 2 (by norm_num) beta (le_trans ha.le hLow)‖ = 1 ∧
        {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 |
          uAIX H beta (le_trans ha.le hLow) B <
            -(mAIX H beta (le_trans ha.le hLow))} =
          p4Q2PZ37AIG_originalNegativeTransferRegion H beta := by
  obtain ⟨N, hN⟩ :=
    p4Q2PZ37AIX_originalNormalizedMargin_window_eventually_small a b eta ha heta
  refine ⟨N, ?_⟩
  intro H hHN beta hLow hHigh
  have hsmall := hN H hHN beta hLow hHigh
  exact ⟨hsmall.1, hsmall.2,
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
      H 2 (by norm_num) beta (le_trans ha.le hLow),
    p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original
      H beta (le_trans ha.le hLow)⟩

/-- The honest normalized source-amplitude upper envelope remains potentially
growing along a bounded coupling window. Its existence is not an amplitude
decay theorem and does not imply a continuum spectral statement. -/
theorem p4Q2PZ37AIX_originalNormalizedSource_windowAmplitudeEnvelope
    (H : ℕ) (a b beta : ℝ) (ha : 0 < a)
    (hLow : a ≤ beta) (hHigh : beta ≤ b)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |uAIX H beta (le_trans ha.le hLow) B| ≤
      (pAIX H / 2) * Real.exp (b * pAIX H) := by
  have hBeta : 0 ≤ beta := le_trans ha.le hLow
  have hp : 0 ≤ pAIX H := (p4Q2PZ37AHN_count_pos H).le
  have hExp : Real.exp (beta * pAIX H) ≤
      Real.exp (b * pAIX H) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hHigh hp)
  calc
    _ ≤ (pAIX H / 2) * Real.exp (beta * pAIX H) :=
      p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_spatialEnvelope
        H beta hBeta B
    _ ≤ _ := mul_le_mul_of_nonneg_left hExp (div_nonneg hp (by norm_num))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! The following seven declarations have separate actual axiom outputs. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedMargin_windowEnvelope_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedMargin_window_eventually_small
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedMargin_couplingSchedule_noPositiveFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedMargin_window_with_physicalOperator
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIX_originalNormalizedSource_windowAmplitudeEnvelope
