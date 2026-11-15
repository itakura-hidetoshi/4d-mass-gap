import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0RawWilsonMomentStepBridgeV5_PZ37ALW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALX — EXACT raw-sector/full-Wilson norm ratio at beta0

The original, unchanged SU(2) Wilson physical one-slab operator P_H acts on
the true gauge-invariant spatial-slice Hilbert space G_H. Its normalized
R_H is restricted to the full top-eigenspace orthogonal K_H at the prescribed
beta0 = log(3/2)/64.

This leaf CONSTRUCTS the genuine unnormalized raw excited-sector map
  A_H : K_H ->L[Real] G_H,   x |-> P_H (x : G_H).
No cross-volume Hilbert map is invented. The previous exact same-volume
normalization bridge proves, for ALL x in K_H:
  ||A_H x|| = ||P_H|| * ||R_H x||.
A generic, separately proved norm-scaling lemma turns this equality of
pointwise norms into the EXACT operator-norm identity
  ||A_H|| = ||P_H|| * ||R_H||,
  ||A_H||^2 = (||R_H||^2) * ||P_H||^2.

Therefore, the new SCALAR, explicitly model-facing two-volume condition
  ||A_(H+1)||^2 <= (q_H + b_H) * ||P_(H+1)||^2,
  q_H = ||R_H||^2
implies the true original-beta0 ALV loss bound L_H<=b_H for b_H>=0.
Unlike ALW, this condition uses the full genuine ||P_H||, NOT the potentially
weak ALJ moment floor F_H. It is exactly normalized, but its cross-volume
bound is still an UNPROVED separate physical estimate.

Summable/geometric scalar certificates feed the ALU/ALV already proved
conditional all-H finite-volume gap criterion. No original Wilson physical
cross-volume estimate, fixed-beta0 all-H gap, Hamiltonian gap, or continuum
Yang-Mills mass gap is asserted here.

One append-only Lean4 leaf; original P, S, K, Haar, AJA, beta0, toolchain,
mathlib and public import roots are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "Q" => p4Q2PZ37ALV_originalFixedExcitedNormSq
local notation "D" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
local notation "Gap" => p4Q2PZ37ALT_originalFixedGapAt

/-- A generic exact operator-norm scaling lemma on one fixed normed carrier.
No Wilson-specific assumptions or cross-H Hilbert identification. -/
theorem p4Q2PZ37ALX_generic_opNorm_eq_of_pointwise_norm_scale
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (B : E →L[ℝ] E)
    (c : ℝ) (hc : 0 < c)
    (hpoint : ∀ x : E, ‖A x‖ = c * ‖B x‖) :
    ‖A‖ = c * ‖B‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hc.le (norm_nonneg B))
    intro x
    calc
      ‖A x‖ = c * ‖B x‖ := hpoint x
      _ ≤ c * (‖B‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm B x) hc.le
      _ = (c * ‖B‖) * ‖x‖ := by ring
  · have hB : ‖B‖ ≤ ‖A‖ / c := by
      apply ContinuousLinearMap.opNorm_le_bound _ (div_nonneg (norm_nonneg A) hc.le)
      intro x
      have hA := ContinuousLinearMap.le_opNorm A x
      rw [hpoint x] at hA
      calc
        ‖B x‖ ≤ (‖A‖ * ‖x‖) / c :=
          (le_div_iff₀ hc).2 (by nlinarith only [hA])
        _ = (‖A‖ / c) * ‖x‖ := by ring
    calc
      c * ‖B‖ ≤ c * (‖A‖ / c) := mul_le_mul_of_nonneg_left hB hc.le
      _ = ‖A‖ := by field_simp [hc.ne']; ring

section GenuinePhysicalVolume
variable (H : ℕ)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- The unnormalized genuine Wilson physical transfer, restricted to the
real original top-orthogonal excited sector K_H and still valued in G_H.
No substitution of a different Wilson kernel or model is involved. -/
noncomputable def p4Q2PZ37ALX_originalFixedRawExcitationMap : K →L[ℝ] G :=
  P.comp K.subtypeL

/-- The true full Wilson one-slab normalization at the original beta0. -/
noncomputable def p4Q2PZ37ALX_originalFixedFullNorm : ℝ := ‖P‖

theorem p4Q2PZ37ALX_originalFixedFullNorm_pos :
    0 < p4Q2PZ37ALX_originalFixedFullNorm H := by
  exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- The true physical raw sector operator norm, independent of ALJ's
moment floor and without comparing carriers at H and H+1. -/
noncomputable def p4Q2PZ37ALX_originalFixedRawExcitationNorm : ℝ :=
  ‖p4Q2PZ37ALX_originalFixedRawExcitationMap H‖

/-- An exact original-Wilson pointwise norm identity on the SAME carrier. -/
theorem p4Q2PZ37ALX_originalFixedRawExcitation_apply_norm
    (x : K) :
    ‖p4Q2PZ37ALX_originalFixedRawExcitationMap H x‖ =
      p4Q2PZ37ALX_originalFixedFullNorm H * ‖R x‖ := by
  have hs :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le x
  change ‖P (x : G)‖ = ‖P‖ * ‖S (x : G)‖
  exact hs.symm

/-- An EXACT, unconditional identity between the true original physical
raw excited operator norm, the genuine full normalizer and the full
top-orthogonal normalized restriction. It involves no ALJ moment estimate. -/
theorem p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq :
    p4Q2PZ37ALX_originalFixedRawExcitationNorm H =
      p4Q2PZ37ALX_originalFixedFullNorm H * ‖R‖ := by
  change ‖p4Q2PZ37ALX_originalFixedRawExcitationMap H‖ = ‖P‖ * ‖R‖
  exact p4Q2PZ37ALX_generic_opNorm_eq_of_pointwise_norm_scale
    (p4Q2PZ37ALX_originalFixedRawExcitationMap H) R ‖P‖
    (p4Q2PZ37ALX_originalFixedFullNorm_pos H)
    (p4Q2PZ37ALX_originalFixedRawExcitation_apply_norm H)

/-- Exact scalar ratio equation for the SAME physical H.
The next-volume comparison remains a distinct, unproved proposition. -/
theorem p4Q2PZ37ALX_originalFixedRawNormSq_eq_ratio :
    p4Q2PZ37ALX_originalFixedRawExcitationNorm H ^ 2 =
      Q H * p4Q2PZ37ALX_originalFixedFullNorm H ^ 2 := by
  rw [p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq]
  change (‖P‖ * ‖R‖) ^ 2 = ‖R‖ ^ 2 * ‖P‖ ^ 2
  ring

end GenuinePhysicalVolume

/-- Cross-volume comparison is now made entirely on TWO REAL-VALUED
norms of the UNCHANGED true physical Wilson operators. This is a
separate physical premise, not an unconditional assertion. -/
def p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate
    (H : ℕ) (b : ℝ) : Prop :=
  p4Q2PZ37ALX_originalFixedRawExcitationNorm (H + 1) ^ 2 ≤
    (Q H + b) * p4Q2PZ37ALX_originalFixedFullNorm (H + 1) ^ 2

/-- The exact raw/full norm identity removes all arbitrary ALJ moment
floor slack from the ALW step. No H-dependent Hilbert operators are
subtracted or identified. -/
theorem p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep
    (H : ℕ) (b : ℝ)
    (hStep : p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate H b) :
    Q (H + 1) ≤ Q H + b := by
  have heq := p4Q2PZ37ALX_originalFixedRawNormSq_eq_ratio (H + 1)
  have hpos :
      0 < p4Q2PZ37ALX_originalFixedFullNorm (H + 1) ^ 2 :=
    sq_pos_of_pos (p4Q2PZ37ALX_originalFixedFullNorm_pos (H + 1))
  apply (mul_le_mul_iff_of_pos_right hpos).mp
  calc
    Q (H + 1) * p4Q2PZ37ALX_originalFixedFullNorm (H + 1) ^ 2 =
        p4Q2PZ37ALX_originalFixedRawExcitationNorm (H + 1) ^ 2 := heq.symm
    _ ≤ (Q H + b) * p4Q2PZ37ALX_originalFixedFullNorm (H + 1) ^ 2 := hStep

theorem p4Q2PZ37ALX_rawNormRatioStep_implies_downwardLoss
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (hStep : p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate H b) :
    p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H ≤ b := by
  exact p4Q2PZ37ALV_oneStepLoss_le_of_normSqIncrease
    H b hb (p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep H b hStep)

/-- The true fixed-beta0 physical gap is uniformly positive under an
INDEPENDENT sum bound on the normalized raw/full Wilson ratio losses.
No physical bound of this kind has been proved. -/
theorem p4Q2PZ37ALX_uniformGap_of_rawNormRatioStepBudget
    (b : ℕ → ℝ) (B : ℝ)
    (hb : ∀ H : ℕ, 0 ≤ b H)
    (hStep : ∀ H : ℕ,
      p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate H (b H))
    (htotal : ∀ H : ℕ, (Finset.range H).sum b ≤ B)
    (hstrict : B < D 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have hD : ∀ H : ℕ, D H ≤ D (H + 1) + b H := by
    intro H
    have hQ := p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep
      H (b H) (hStep H)
    rw [p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq H,
      p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq (H + 1)]
    linarith
  exact p4Q2PZ37ALU_originalFixedUniformGap_of_stepwiseBudget
    b B hb hD htotal hstrict

/-- The physical Wilson raw/full norm-squared cross-volume inequality is
sufficient if independent geometric constants give a small total loss. -/
theorem p4Q2PZ37ALX_uniformGap_of_geometricRawNormRatioStep
    (C r : ℝ) (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hSmall : C < (1 - r) * D 0)
    (hStep : ∀ H : ℕ,
      p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate H (C * r ^ H)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  apply p4Q2PZ37ALV_uniformGap_of_global_geometricNormSqStep
    C r hC hr0 hr1 hSmall
  intro H
  exact p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep
    H (C * r ^ H) (hStep H)

/-- The geometric physical Wilson ratio bound need only be established
after a finite prefix M when ALT handles the prefix exactly. -/
theorem p4Q2PZ37ALX_uniformGap_of_tail_geometricRawNormRatioStep
    (M : ℕ) (C r : ℝ)
    (hC : 0 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hSmall : C < (1 - r) * D M)
    (hStep : ∀ n : ℕ,
      p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate
        (M + n) (C * r ^ n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  apply p4Q2PZ37ALV_uniformGap_of_tail_geometricNormSqStep
    M C r hC hr0 hr1 hSmall
  intro n
  exact p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep
    (M + n) (C * r ^ n) (hStep n)

/-- A directly observable ratio growth exceeding b refutes the alleged
cross-volume raw/full physical norm ratio certificate. -/
theorem p4Q2PZ37ALX_rawNormRatioStep_impossible_of_excess
    (H : ℕ) (b : ℝ)
    (hExcess : Q H + b < Q (H + 1)) :
    ¬ p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate H b := by
  intro hs
  have h := p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep H b hs
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_generic_opNorm_eq_of_pointwise_norm_scale
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedRawExcitationMap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedFullNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedFullNorm_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedRawExcitationNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedRawExcitation_apply_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedRawNormSq_eq_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_originalFixedRawNormRatioStepCertificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_rawNormRatioStep_implies_excitedNormSqStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_rawNormRatioStep_implies_downwardLoss
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_uniformGap_of_rawNormRatioStepBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_uniformGap_of_geometricRawNormRatioStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_uniformGap_of_tail_geometricRawNormRatioStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALX_rawNormRatioStep_impossible_of_excess
