import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelBidirectionalFiniteResponseMonotone
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators

noncomputable section

/-- The volume-independent limiting response obtained after the finite
random-scan terminal residual has been sent to zero. -/
def finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
    (coefficient envelopeMagnitude sourceMagnitude : ℝ) : ℝ :=
  envelopeMagnitude * sourceMagnitude * (1 - coefficient)⁻¹

/-- The reciprocal random-scan rate lies strictly below one whenever the
underlying row or column coefficient does. -/
theorem finiteInfluenceKernelReciprocalRandomScanRate_lt_one
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    {coefficient : ℝ}
    (hCoefficient : coefficient < 1) :
    finiteInfluenceKernelReciprocalRandomScanRate ι coefficient < 1 := by
  have hCardReal : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hCard
  unfold finiteInfluenceKernelReciprocalRandomScanRate
  calc
    ((Fintype.card ι : ℝ) - 1 + coefficient) *
        (Fintype.card ι : ℝ)⁻¹ <
      (Fintype.card ι : ℝ) * (Fintype.card ι : ℝ)⁻¹ := by
        apply mul_lt_mul_of_pos_right
        · linarith
        · exact inv_pos.mpr hCardReal
    _ = 1 := by
      exact mul_inv_cancel₀ (ne_of_gt hCardReal)

/-- Exact complement of the reciprocal random-scan rate. -/
theorem one_sub_finiteInfluenceKernelReciprocalRandomScanRate
    {ι : Type}
    [Fintype ι]
    (coefficient : ℝ) :
    1 - finiteInfluenceKernelReciprocalRandomScanRate ι coefficient =
      (1 - coefficient) * (Fintype.card ι : ℝ)⁻¹ := by
  unfold finiteInfluenceKernelReciprocalRandomScanRate
  ring

/-- Finite geometric-series identity in the convention used by the response
kernel. -/
theorem one_sub_mul_finiteRealGeometricSeries
    (rate : ℝ)
    (iterations : ℕ) :
    (1 - rate) * finiteRealGeometricSeries rate iterations =
      1 - rate ^ iterations := by
  induction iterations with
  | zero => simp [finiteRealGeometricSeries]
  | succ iterations ih =>
      rw [finiteRealGeometricSeries_succ, pow_succ]
      calc
        (1 - rate) *
            (finiteRealGeometricSeries rate iterations + rate ^ iterations) =
          (1 - rate) * finiteRealGeometricSeries rate iterations +
            (1 - rate) * rate ^ iterations := by ring
        _ = (1 - rate ^ iterations) +
            (1 - rate) * rate ^ iterations := by rw [ih]
        _ = 1 - rate ^ iterations * rate := by ring

/-- After the averaging factor `|ι|⁻¹`, every finite geometric prefix is
bounded by the exact infinite response denominator `(1-a)⁻¹`. -/
theorem inv_card_mul_finiteRealGeometricSeries_le_one_sub_inv
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    {coefficient : ℝ}
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1)
    (iterations : ℕ) :
    (Fintype.card ι : ℝ)⁻¹ *
        finiteRealGeometricSeries
          (finiteInfluenceKernelReciprocalRandomScanRate ι coefficient)
          iterations ≤
      (1 - coefficient)⁻¹ := by
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate ι coefficient
  have hCardReal : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast hCard
  have hRateNonneg : 0 ≤ rate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard coefficient hCoefficientNonneg
  have hOneSubCoefficient : 0 < 1 - coefficient := by linarith
  have hSeriesNonneg :
      0 ≤ finiteRealGeometricSeries rate iterations := by
    unfold finiteRealGeometricSeries
    exact Finset.sum_nonneg fun k _hk => pow_nonneg hRateNonneg k
  have hIdentity :=
    one_sub_mul_finiteRealGeometricSeries rate iterations
  have hRatePowNonneg : 0 ≤ rate ^ iterations :=
    pow_nonneg hRateNonneg iterations
  have hProductLeOne :
      (1 - rate) * finiteRealGeometricSeries rate iterations ≤ 1 := by
    rw [hIdentity]
    linarith
  change (Fintype.card ι : ℝ)⁻¹ *
      finiteRealGeometricSeries rate iterations ≤
        (1 - coefficient)⁻¹
  rw [show (1 - coefficient)⁻¹ = 1 / (1 - coefficient) by
    simp [div_eq_mul_inv]]
  apply (le_div_iff₀ hOneSubCoefficient).2
  calc
    ((Fintype.card ι : ℝ)⁻¹ *
          finiteRealGeometricSeries rate iterations) *
        (1 - coefficient) =
      (1 - rate) * finiteRealGeometricSeries rate iterations := by
        rw [one_sub_finiteInfluenceKernelReciprocalRandomScanRate]
        ring
    _ ≤ 1 := hProductLeOne

/-- Every strict finite response is bounded by its volume-independent
asymptotic response plus the explicit finite terminal residual. -/
theorem finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_le_asymptotic_add_terminal
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    (iterations : ℕ)
    {coefficient envelopeMagnitude sourceMagnitude : ℝ}
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1)
    (hEnvelopeMagnitude : 0 ≤ envelopeMagnitude)
    (hSourceMagnitude : 0 ≤ sourceMagnitude) :
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        ι iterations coefficient envelopeMagnitude sourceMagnitude ≤
      finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
          coefficient envelopeMagnitude sourceMagnitude +
        2 * (Fintype.card ι : ℝ) *
          (finiteInfluenceKernelReciprocalRandomScanRate
              ι coefficient ^ iterations * sourceMagnitude) := by
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate ι coefficient
  have hPrefix :=
    inv_card_mul_finiteRealGeometricSeries_le_one_sub_inv
      hCard hCoefficientNonneg hCoefficientLtOne iterations
  have hMagnitude : 0 ≤ envelopeMagnitude * sourceMagnitude :=
    mul_nonneg hEnvelopeMagnitude hSourceMagnitude
  have hPrefixScaled :
      envelopeMagnitude * sourceMagnitude *
          ((Fintype.card ι : ℝ)⁻¹ *
            finiteRealGeometricSeries rate iterations) ≤
        envelopeMagnitude * sourceMagnitude * (1 - coefficient)⁻¹ :=
    mul_le_mul_of_nonneg_left hPrefix hMagnitude
  unfold finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
    finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
  change
    (Fintype.card ι : ℝ)⁻¹ * envelopeMagnitude * sourceMagnitude *
          finiteRealGeometricSeries rate iterations +
        2 * (Fintype.card ι : ℝ) *
          (rate ^ iterations * sourceMagnitude) ≤
      envelopeMagnitude * sourceMagnitude * (1 - coefficient)⁻¹ +
        2 * (Fintype.card ι : ℝ) *
          (rate ^ iterations * sourceMagnitude)
  apply add_le_add_right _ _
  calc
    (Fintype.card ι : ℝ)⁻¹ * envelopeMagnitude * sourceMagnitude *
        finiteRealGeometricSeries rate iterations =
      envelopeMagnitude * sourceMagnitude *
        ((Fintype.card ι : ℝ)⁻¹ *
          finiteRealGeometricSeries rate iterations) := by ring
    _ ≤ envelopeMagnitude * sourceMagnitude * (1 - coefficient)⁻¹ :=
      hPrefixScaled

/-- A nonnegative geometric terminal residual with strict ratio can be made
smaller than any positive tolerance at a finite iteration depth. -/
theorem exists_finite_geometric_terminal_le
    (amplitude rate tolerance : ℝ)
    (hAmplitude : 0 ≤ amplitude)
    (hRateNonneg : 0 ≤ rate)
    (hRateLtOne : rate < 1)
    (hTolerance : 0 < tolerance) :
    ∃ iterations : ℕ, amplitude * rate ^ iterations ≤ tolerance := by
  have hTendsto :
      Tendsto (fun n : ℕ => amplitude * rate ^ n) atTop (nhds 0) := by
    have hRateTendsto :
        Tendsto (fun n : ℕ => rate ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
    simpa using tendsto_const_nhds.mul hRateTendsto
  have hEventually :
      ∀ᶠ n : ℕ in atTop, amplitude * rate ^ n < tolerance :=
    (tendsto_order.1 hTendsto).2 tolerance hTolerance
  rcases (eventually_atTop.1 hEventually) with ⟨iterations, hIterations⟩
  exact ⟨iterations, le_of_lt (hIterations iterations le_rfl)⟩

/-- Finite-depth realization of any strict asymptotic response margin. -/
theorem exists_finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_lt
    {ι : Type}
    [Fintype ι]
    (hCard : 0 < Fintype.card ι)
    {coefficient envelopeMagnitude sourceMagnitude bound : ℝ}
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1)
    (hEnvelopeMagnitude : 0 ≤ envelopeMagnitude)
    (hSourceMagnitude : 0 ≤ sourceMagnitude)
    (hAsymptotic :
      finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
          coefficient envelopeMagnitude sourceMagnitude < bound) :
    ∃ iterations : ℕ,
      finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
          ι iterations coefficient envelopeMagnitude sourceMagnitude < bound := by
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate ι coefficient
  let asymptotic :=
    finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
      coefficient envelopeMagnitude sourceMagnitude
  let amplitude :=
    2 * (Fintype.card ι : ℝ) * sourceMagnitude
  let tolerance := bound - asymptotic
  have hRateNonneg : 0 ≤ rate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCard coefficient hCoefficientNonneg
  have hRateLtOne : rate < 1 :=
    finiteInfluenceKernelReciprocalRandomScanRate_lt_one
      hCard hCoefficientLtOne
  have hAmplitude : 0 ≤ amplitude :=
    mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
      hSourceMagnitude
  have hTolerance : 0 < tolerance := by
    simpa [tolerance, asymptotic] using sub_pos.mpr hAsymptotic
  obtain ⟨iterations, hTerminal⟩ :=
    exists_finite_geometric_terminal_le
      amplitude rate tolerance hAmplitude hRateNonneg hRateLtOne hTolerance
  refine ⟨iterations, ?_⟩
  have hFinite :=
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_le_asymptotic_add_terminal
      hCard iterations hCoefficientNonneg hCoefficientLtOne
      hEnvelopeMagnitude hSourceMagnitude
  have hTerminal' :
      2 * (Fintype.card ι : ℝ) *
          (rate ^ iterations * sourceMagnitude) ≤ tolerance := by
    simpa [amplitude] using hTerminal
  calc
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        ι iterations coefficient envelopeMagnitude sourceMagnitude ≤
      asymptotic +
        2 * (Fintype.card ι : ℝ) *
          (rate ^ iterations * sourceMagnitude) := by
            simpa [asymptotic, rate] using hFinite
    _ ≤ asymptotic + tolerance := add_le_add_left hTerminal' asymptotic
    _ = bound := by simp [tolerance]

end

end MathlibAnalytic
end MGAP4D