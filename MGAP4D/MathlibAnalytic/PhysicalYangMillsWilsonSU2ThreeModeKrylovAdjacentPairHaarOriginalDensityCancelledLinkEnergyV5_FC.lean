import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalKernelL2SupPhysicalSourceV5_FB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarExactJointHalfDensityMoments
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHalfDensityLocalHarnack
import Mathlib.Tactic

/-!
# P4-Q2-FC: original Wilson half-density cancellation in physical link energy

The original signed joint observable is the physical W_beta * M_beta,f,
not a substitute Haar posterior. Rather than taking the suprema of
W_beta and the inverse continuous vacuum separately, retain their
pointwise product W_beta(z) * Omega_beta(B)^(-1) and use the existing
EXACT original Wilson joint-square moment identity

  integral (W_beta(z) * Omega_beta(B)^(-1))² d pi_beta(z)
    = ||T_beta||^(-2).

The first stage below proves a genuinely POINTWISE one-link estimate
for the signed original physical observable, with its full output
drift and positive-beta Wilson posterior retained. The frozen beta and
fine beta remain distinct, and no bounded-sup or volume-uniform
physical hypothesis is inserted.

Unlike arbitrary L² functions, the physical source is smoothed by
the genuine positive Wilson kernel and existing normalized transfer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 900000

private theorem p4Q2FC_signed_product_local_ratio
    (R w w' m m' t : ℝ)
    (hR : 1 ≤ R) (hw : 0 ≤ w) (hw' : 0 ≤ w')
    (hForward : w' ≤ R * w) (hBackward : w ≤ R * w')
    (hMean : |m| ≤ t)
    (hMeanDifference : |m - m'| ≤ (R ^ 2 - 1) * t)
    (ht : 0 ≤ t) :
    |w * m - w' * m'| ≤ (R ^ 3 - 1) * w * t := by
  have hRm : 0 ≤ R - 1 := sub_nonneg.mpr hR
  have hR2 : 0 ≤ R ^ 2 - 1 := by nlinarith [hR]
  have hAbsW : |w - w'| ≤ (R - 1) * w := by
    have hUpper : w' - w ≤ (R - 1) * w := by nlinarith [hForward]
    have hLower : w - w' ≤ (R - 1) * w := by
      by_cases hww : w' ≤ w
      · have hOne : w - w' ≤ (R - 1) * w' := by nlinarith [hBackward]
        have hTwo : (R - 1) * w' ≤ (R - 1) * w :=
          mul_le_mul_of_nonneg_left hww hRm
        exact hOne.trans hTwo
      · linarith
    exact abs_le.mpr ⟨by linarith, hLower⟩
  have hNonneg : 0 ≤ (R ^ 2 - 1) * t := mul_nonneg hR2 ht
  have hFirst : |w' * (m - m')| ≤ (R * w) * ((R ^ 2 - 1) * t) := by
    calc
      |w' * (m - m')| = w' * |m - m'| := by
        rw [abs_mul, abs_of_nonneg hw']
      _ ≤ w' * ((R ^ 2 - 1) * t) :=
        mul_le_mul_of_nonneg_left hMeanDifference hw'
      _ ≤ (R * w) * ((R ^ 2 - 1) * t) :=
        mul_le_mul_of_nonneg_right hForward hNonneg
  have hSecond : |(w - w') * m| ≤ ((R - 1) * w) * t := by
    calc
      |(w - w') * m| = |w - w'| * |m| := abs_mul _ _
      _ ≤ ((R - 1) * w) * |m| :=
        mul_le_mul_of_nonneg_right hAbsW (abs_nonneg m)
      _ ≤ ((R - 1) * w) * t :=
        mul_le_mul_of_nonneg_left hMean (mul_nonneg hRm hw)
  calc
    |w * m - w' * m'| =
        |w' * (m - m') + (w - w') * m| := by
          congr 1
          ring
    _ ≤ |w' * (m - m')| + |(w - w') * m| :=
      abs_add_le _ _
    _ ≤ (R * w) * ((R ^ 2 - 1) * t) + ((R - 1) * w) * t :=
      add_le_add hFirst hSecond
    _ = (R ^ 3 - 1) * w * t := by ring

namespace GroundStatePosteriorJoint

/-- True original Wilson signed right-link observable variation is
bounded by the ACTUAL pointwise half-density / inverse-vacuum product.
No global supremum of either factor and no fake independent posterior.
The local multiplier exp(8 beta)^3 - 1 vanishes at frozen beta zero. -/
theorem p4Q2FC_originalJointReceiver_linkDifference_abs_le_weightedSource
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (z : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
    let L := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
    let R := Real.exp (8 * beta)
    let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
    |O z - O (z.1, Function.update z.2 e g)| ≤
      L * (R ^ 3 - 1) * ‖f‖ * (W z * V z.2) := by
  classical
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let M := normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
  let O := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
    H N hN beta hbeta
  let L : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let zp := (z.1, Function.update z.2 e g)
  let t : ℝ := L * V z.2 * ‖f‖
  have hL : 0 ≤ L :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  have hR : 1 ≤ R := by
    change 1 ≤ Real.exp (8 * beta)
    have hb : (0 : ℝ) ≤ 8 * beta := by positivity
    simpa using
      (Real.exp_le_exp.mpr hb : Real.exp (0 : ℝ) ≤ Real.exp (8 * beta))
  have hOmega (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      0 < Ω B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  have hWnonneg (q :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
      0 ≤ W q := by
    change 0 ≤ (L * Ω q.2) / continuousJointSqrtDensity H N hN beta hbeta q
    exact div_nonneg
      (mul_nonneg hL (hOmega q.2).le)
      (continuousJointSqrtDensity_pos H N hN beta hbeta q).le
  have hWF : W zp ≤ R * W z :=
    normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
      H N hN beta hbeta e z g
  have hWB : W z ≤ R * W zp := by
    have h := normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightUpdate_le_exp_eight_mul
      H N hN beta hbeta e zp (z.2 e)
    change W (z.1, Function.update (Function.update z.2 e g) e (z.2 e)) ≤
      R * W zp at h
    simpa using h
  have hV : 0 ≤ V z.2 := by
    change 0 ≤ (Ω z.2)⁻¹
    exact (inv_pos.mpr (hOmega z.2)).le
  have ht : 0 ≤ t := by
    dsimp [t]
    positivity
  have hMean :
      |M z| ≤ t := by
    have h :=
      p4Q2FB_originalVacuumMean_weighted_abs_le_sourceL2
        H N hN beta hbeta f z.2
    change Ω z.2 * |M z| ≤ L * ‖f‖ at h
    have hi := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (hOmega z.2).le)
    calc
      |M z| = (Ω z.2)⁻¹ * (Ω z.2 * |M z|) := by
        rw [← mul_assoc, inv_mul_cancel₀ (hOmega z.2).ne', one_mul]
      _ ≤ (Ω z.2)⁻¹ * (L * ‖f‖) := hi
      _ = t := by
        change (Ω z.2)⁻¹ * (L * ‖f‖) = L * (Ω z.2)⁻¹ * ‖f‖
        ring
  have hMeanDifference :
      |M z - M zp| ≤ (R ^ 2 - 1) * t := by
    have h := normalizedPhysicalOneSlabVacuumReceiverBCF_rightLinkDifference_abs_le_signedSourceL2
      H N hN beta hbeta f z.2 e g
    change |M zp - M z| ≤
      L * ((R ^ 2 - 1) / Ω z.2) * ‖f‖ at h
    calc
      |M z - M zp| = |M zp - M z| := abs_sub_comm _ _
      _ ≤ L * ((R ^ 2 - 1) / Ω z.2) * ‖f‖ := h
      _ = (R ^ 2 - 1) * t := by
        change L * ((R ^ 2 - 1) / Ω z.2) * ‖f‖ =
          (R ^ 2 - 1) * (L * (Ω z.2)⁻¹ * ‖f‖)
        rw [div_eq_mul_inv]
        ring
  have hScalar := p4Q2FC_signed_product_local_ratio
    R (W z) (W zp) (M z) (M zp) t
    hR (hWnonneg z) (hWnonneg zp) hWF hWB hMean hMeanDifference ht
  change |W z * M z - W zp * M zp| ≤
    L * (R ^ 3 - 1) * ‖f‖ * (W z * V z.2)
  calc
    |W z * M z - W zp * M zp| ≤
      (R ^ 3 - 1) * W z * t := hScalar
    _ = L * (R ^ 3 - 1) * ‖f‖ * (W z * V z.2) := by
      dsimp [t]
      ring

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FC_originalJointReceiver_linkDifference_abs_le_weightedSource
