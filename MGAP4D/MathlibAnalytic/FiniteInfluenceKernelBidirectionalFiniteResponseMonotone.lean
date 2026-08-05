import MGAP4D.MathlibAnalytic.FinitePositiveWeightBidirectionalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The reciprocal random-scan rate is monotone in the declared row or column
coefficient. -/
theorem finiteInfluenceKernelReciprocalRandomScanRate_mono
    {ι : Type}
    [Fintype ι]
    {leftCoefficient rightCoefficient : ℝ}
    (hCoefficient : leftCoefficient ≤ rightCoefficient) :
    finiteInfluenceKernelReciprocalRandomScanRate
        ι leftCoefficient ≤
      finiteInfluenceKernelReciprocalRandomScanRate
        ι rightCoefficient := by
  unfold finiteInfluenceKernelReciprocalRandomScanRate
  apply mul_le_mul_of_nonneg_left
  · linarith
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- Powers are monotone between nonnegative real bases. -/
theorem finiteRealPow_le_pow_of_nonneg
    {left right : ℝ}
    (hLeft : 0 ≤ left)
    (hLeftRight : left ≤ right)
    (n : ℕ) :
    left ^ n ≤ right ^ n := by
  have hRight : 0 ≤ right := hLeft.trans hLeftRight
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      calc
        left ^ n * left ≤ right ^ n * left :=
          mul_le_mul_of_nonneg_right ih hLeft
        _ ≤ right ^ n * right :=
          mul_le_mul_of_nonneg_left hLeftRight (pow_nonneg hRight n)

/-- Finite real geometric sums are monotone between nonnegative bases. -/
theorem finiteRealGeometricSeries_mono_of_nonneg
    {left right : ℝ}
    (hLeft : 0 ≤ left)
    (hLeftRight : left ≤ right)
    (n : ℕ) :
    finiteRealGeometricSeries left n ≤
      finiteRealGeometricSeries right n := by
  induction n with
  | zero => simp [finiteRealGeometricSeries]
  | succ n ih =>
      rw [finiteRealGeometricSeries_succ,
        finiteRealGeometricSeries_succ]
      exact add_le_add ih
        (finiteRealPow_le_pow_of_nonneg hLeft hLeftRight n)

/-- The shared finite bidirectional response coefficient is monotone in the
row or column coefficient whenever all physical amplitudes are nonnegative. -/
theorem finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_mono
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (iterations : ℕ)
    {leftCoefficient rightCoefficient envelopeMagnitude sourceMagnitude : ℝ}
    (hLeftCoefficient : 0 ≤ leftCoefficient)
    (hCoefficient : leftCoefficient ≤ rightCoefficient)
    (hEnvelopeMagnitude : 0 ≤ envelopeMagnitude)
    (hSourceMagnitude : 0 ≤ sourceMagnitude) :
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        ι iterations leftCoefficient envelopeMagnitude sourceMagnitude ≤
      finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        ι iterations rightCoefficient envelopeMagnitude sourceMagnitude := by
  let leftRate :=
    finiteInfluenceKernelReciprocalRandomScanRate ι leftCoefficient
  let rightRate :=
    finiteInfluenceKernelReciprocalRandomScanRate ι rightCoefficient
  have hRightCoefficient : 0 ≤ rightCoefficient :=
    hLeftCoefficient.trans hCoefficient
  have hLeftRate : 0 ≤ leftRate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard leftCoefficient hLeftCoefficient
  have hRightRate : 0 ≤ rightRate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard rightCoefficient hRightCoefficient
  have hRate : leftRate ≤ rightRate := by
    exact finiteInfluenceKernelReciprocalRandomScanRate_mono hCoefficient
  have hSeries :
      finiteRealGeometricSeries leftRate iterations ≤
        finiteRealGeometricSeries rightRate iterations :=
    finiteRealGeometricSeries_mono_of_nonneg
      hLeftRate hRate iterations
  have hPower :
      leftRate ^ iterations ≤ rightRate ^ iterations :=
    finiteRealPow_le_pow_of_nonneg hLeftRate hRate iterations
  have hPrefixFactor :
      0 ≤ (Fintype.card ι : ℝ)⁻¹ *
        envelopeMagnitude * sourceMagnitude :=
    mul_nonneg
      (mul_nonneg
        (inv_nonneg.mpr (Nat.cast_nonneg _))
        hEnvelopeMagnitude)
      hSourceMagnitude
  have hPrefix :
      (Fintype.card ι : ℝ)⁻¹ * envelopeMagnitude * sourceMagnitude *
          finiteRealGeometricSeries leftRate iterations ≤
        (Fintype.card ι : ℝ)⁻¹ * envelopeMagnitude * sourceMagnitude *
          finiteRealGeometricSeries rightRate iterations :=
    mul_le_mul_of_nonneg_left hSeries hPrefixFactor
  have hTerminalInner :
      leftRate ^ iterations * sourceMagnitude ≤
        rightRate ^ iterations * sourceMagnitude :=
    mul_le_mul_of_nonneg_right hPower hSourceMagnitude
  have hTerminalFactor :
      0 ≤ 2 * (Fintype.card ι : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hTerminal :
      2 * (Fintype.card ι : ℝ) *
          (leftRate ^ iterations * sourceMagnitude) ≤
        2 * (Fintype.card ι : ℝ) *
          (rightRate ^ iterations * sourceMagnitude) :=
    mul_le_mul_of_nonneg_left hTerminalInner hTerminalFactor
  simpa [finiteInfluenceKernelBidirectionalFiniteResponseCoefficient,
    leftRate, rightRate] using add_le_add hPrefix hTerminal

end

end MathlibAnalytic
end MGAP4D