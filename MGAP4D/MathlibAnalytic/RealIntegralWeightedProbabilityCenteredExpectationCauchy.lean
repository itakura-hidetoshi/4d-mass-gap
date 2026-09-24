import MGAP4D.MathlibAnalytic.LikelihoodRatioCenteredExpectationCauchy
import MGAP4D.MathlibAnalytic.RealIntegralWeightedProbabilityNormalization
import Mathlib.Tactic

/-!
# Centered expectation Cauchy transport for normalized real weights

This file packages the generic density theorem from
LikelihoodRatioCenteredExpectationCauchy directly at the level of the
repository's normalized real weighted probability measures.

If two nonnegative weights w and v are mutually pointwise R-comparable, then
normalization costs one further factor R, so the normalized densities are
mutually R^2-comparable.  Therefore centered expectation transport is bounded
by the full-L1 coefficient attached to R^2 times the square root of the sum of
the two centered energies.

The theorem deliberately keeps the first- and second-moment integrability
receipts explicit.  In the bounded-concrete physical application these are
automatic from boundedness and the already-established fiber integrability.
No volume/cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

namespace HaarLikelihoodRatioInfluence

/-- Mutually comparable nonnegative real weights yield an L2 centered
expectation comparison after normalization.

The coefficient is the normalized-law coefficient associated with R^2:
normalization of mutually R-comparable weights costs one further factor R. -/
theorem realIntegralWeightedProbabilityMeasure_centered_integral_sub_abs_le_fullL1_coefficient_mul_sqrt_energy
    {α : Type*}
    [MeasurableSpace α]
    (μ : Measure α)
    (w v X : α → ℝ)
    (hwMeas : Measurable w)
    (hvMeas : Measurable v)
    (hwInt : Integrable w μ)
    (hvInt : Integrable v μ)
    (hw0 : ∀ x, 0 ≤ w x)
    (hv0 : ∀ x, 0 ≤ v x)
    (hwMassPos : 0 < ∫ x, w x ∂μ)
    (hvMassPos : 0 < ∫ x, v x ∂μ)
    (R : ℝ)
    (hR : 1 ≤ R)
    (hwv : ∀ x, w x ≤ R * v x)
    (hvw : ∀ x, v x ≤ R * w x)
    (hX : StronglyMeasurable X)
    (center : ℝ)
    (hFirstW : Integrable (fun x => w x * (X x - center)) μ)
    (hFirstV : Integrable (fun x => v x * (X x - center)) μ)
    (hEnergyW : Integrable (fun x => w x * (X x - center) ^ 2) μ)
    (hEnergyV : Integrable (fun x => v x * (X x - center) ^ 2) μ) :
    |(∫ x, X x - center ∂realIntegralWeightedProbabilityMeasure μ w) -
        (∫ x, X x - center ∂realIntegralWeightedProbabilityMeasure μ v)| ≤
      (2 * coefficient (R ^ 2)) *
        Real.sqrt
          ((∫ x, (X x - center) ^ 2
              ∂realIntegralWeightedProbabilityMeasure μ w) +
            ∫ x, (X x - center) ^ 2
              ∂realIntegralWeightedProbabilityMeasure μ v) := by
  let Zw : ℝ := ∫ x, w x ∂μ
  let Zv : ℝ := ∫ x, v x ∂μ
  let p : α → ℝ := fun x => w x / Zw
  let q : α → ℝ := fun x => v x / Zv
  let K : ℝ := R ^ 2

  have hZw : 0 < Zw := by simpa [Zw] using hwMassPos
  have hZv : 0 < Zv := by simpa [Zv] using hvMassPos
  have hR0 : 0 ≤ R := le_trans zero_le_one hR
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg (R - 1)]

  have hZwLe : Zw ≤ R * Zv := by
    dsimp [Zw, Zv]
    calc
      (∫ x, w x ∂μ) ≤ ∫ x, R * v x ∂μ := by
        exact integral_mono hwInt (hvInt.const_mul R) hwv
      _ = R * ∫ x, v x ∂μ := by rw [integral_const_mul]

  have hZvLe : Zv ≤ R * Zw := by
    dsimp [Zw, Zv]
    calc
      (∫ x, v x ∂μ) ≤ ∫ x, R * w x ∂μ := by
        exact integral_mono hvInt (hwInt.const_mul R) hvw
      _ = R * ∫ x, w x ∂μ := by rw [integral_const_mul]

  have hpMeas : Measurable p := by
    dsimp [p]
    exact hwMeas.div measurable_const
  have hqMeas : Measurable q := by
    dsimp [q]
    exact hvMeas.div measurable_const

  have hpInt : Integrable p μ := by
    have h := hwInt.const_mul Zw⁻¹
    apply h.congr
    filter_upwards with x
    simp [p, div_eq_mul_inv, mul_comm]
  have hqInt : Integrable q μ := by
    have h := hvInt.const_mul Zv⁻¹
    apply h.congr
    filter_upwards with x
    simp [q, div_eq_mul_inv, mul_comm]

  have hp0 : ∀ x, 0 ≤ p x := by
    intro x
    exact div_nonneg (hw0 x) hZw.le
  have hq0 : ∀ x, 0 ≤ q x := by
    intro x
    exact div_nonneg (hv0 x) hZv.le

  have hpOne : ∫ x, p x ∂μ = 1 := by
    dsimp [p]
    rw [integral_div]
    exact div_self (ne_of_gt hZw)
  have hqOne : ∫ x, q x ∂μ = 1 := by
    dsimp [q]
    rw [integral_div]
    exact div_self (ne_of_gt hZv)

  have hpq : ∀ x, p x ≤ K * q x := by
    intro x
    have hCross :
        w x * Zv ≤ (R ^ 2 * v x) * Zw := by
      calc
        w x * Zv ≤ (R * v x) * Zv :=
          mul_le_mul_of_nonneg_right (hwv x) hZv.le
        _ ≤ (R * v x) * (R * Zw) :=
          mul_le_mul_of_nonneg_left hZvLe
            (mul_nonneg hR0 (hv0 x))
        _ = (R ^ 2 * v x) * Zw := by ring
    have hDiv :
        w x / Zw ≤ (R ^ 2 * v x) / Zv :=
      (div_le_div_iff₀ hZw hZv).2 hCross
    simpa [p, q, K, mul_div_assoc] using hDiv

  have hqp : ∀ x, q x ≤ K * p x := by
    intro x
    have hCross :
        v x * Zw ≤ (R ^ 2 * w x) * Zv := by
      calc
        v x * Zw ≤ (R * w x) * Zw :=
          mul_le_mul_of_nonneg_right (hvw x) hZw.le
        _ ≤ (R * w x) * (R * Zv) :=
          mul_le_mul_of_nonneg_left hZwLe
            (mul_nonneg hR0 (hw0 x))
        _ = (R ^ 2 * w x) * Zv := by ring
    have hDiv :
        v x / Zv ≤ (R ^ 2 * w x) / Zw :=
      (div_le_div_iff₀ hZv hZw).2 hCross
    simpa [p, q, K, mul_div_assoc] using hDiv

  have hFirstP :
      Integrable (fun x => (X x - center) * p x) μ := by
    have h := hFirstW.const_mul Zw⁻¹
    apply h.congr
    filter_upwards with x
    simp [p, div_eq_mul_inv]
    ring
  have hFirstQ :
      Integrable (fun x => (X x - center) * q x) μ := by
    have h := hFirstV.const_mul Zv⁻¹
    apply h.congr
    filter_upwards with x
    simp [q, div_eq_mul_inv]
    ring

  have hEnergyP :
      Integrable (fun x => (X x - center) ^ 2 * p x) μ := by
    have h := hEnergyW.const_mul Zw⁻¹
    apply h.congr
    filter_upwards with x
    simp [p, div_eq_mul_inv]
    ring
  have hEnergyQ :
      Integrable (fun x => (X x - center) ^ 2 * q x) μ := by
    have h := hEnergyV.const_mul Zv⁻¹
    apply h.congr
    filter_upwards with x
    simp [q, div_eq_mul_inv]
    ring

  have hEnergy :
      Integrable
        (fun x => (X x - center) ^ 2 * (p x + q x)) μ := by
    apply (hEnergyP.add hEnergyQ).congr
    filter_upwards with x
    ring

  have hCore :=
    centered_density_difference_integral_abs_le_fullL1_coefficient_mul_sqrt_energy
      μ p q hpMeas hqMeas hpInt hqInt hp0 hq0 hpOne hqOne
      K hK (fun x => ⟨hpq x, hqp x⟩)
      X hX center hEnergy

  have hCenteredW :
      (∫ x, X x - center
          ∂realIntegralWeightedProbabilityMeasure μ w) =
        ∫ x, (X x - center) * p x ∂μ := by
    have hNorm :=
      realIntegralWeightedProbabilityMeasure_integral
        μ w (fun x => X x - center) hwInt
        (Filter.Eventually.of_forall hw0) hwMassPos
    calc
      (∫ x, X x - center
          ∂realIntegralWeightedProbabilityMeasure μ w) =
          Zw⁻¹ * ∫ x, w x * (X x - center) ∂μ := by
        simpa [Zw] using hNorm
      _ = ∫ x, Zw⁻¹ * (w x * (X x - center)) ∂μ := by
        rw [integral_const_mul]
      _ = ∫ x, (X x - center) * p x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [p, div_eq_mul_inv]
        ring

  have hCenteredV :
      (∫ x, X x - center
          ∂realIntegralWeightedProbabilityMeasure μ v) =
        ∫ x, (X x - center) * q x ∂μ := by
    have hNorm :=
      realIntegralWeightedProbabilityMeasure_integral
        μ v (fun x => X x - center) hvInt
        (Filter.Eventually.of_forall hv0) hvMassPos
    calc
      (∫ x, X x - center
          ∂realIntegralWeightedProbabilityMeasure μ v) =
          Zv⁻¹ * ∫ x, v x * (X x - center) ∂μ := by
        simpa [Zv] using hNorm
      _ = ∫ x, Zv⁻¹ * (v x * (X x - center)) ∂μ := by
        rw [integral_const_mul]
      _ = ∫ x, (X x - center) * q x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, div_eq_mul_inv]
        ring

  have hDensityCentered :
      (∫ x, (X x - center) * p x ∂μ) -
          (∫ x, (X x - center) * q x ∂μ) =
        ∫ x, (X x - center) * (p x - q x) ∂μ := by
    rw [← integral_sub hFirstP hFirstQ]
    apply integral_congr_ae
    filter_upwards with x
    ring

  have hEnergyWMeasure :
      (∫ x, (X x - center) ^ 2
          ∂realIntegralWeightedProbabilityMeasure μ w) =
        ∫ x, (X x - center) ^ 2 * p x ∂μ := by
    have hNorm :=
      realIntegralWeightedProbabilityMeasure_integral
        μ w (fun x => (X x - center) ^ 2) hwInt
        (Filter.Eventually.of_forall hw0) hwMassPos
    calc
      (∫ x, (X x - center) ^ 2
          ∂realIntegralWeightedProbabilityMeasure μ w) =
          Zw⁻¹ * ∫ x, w x * (X x - center) ^ 2 ∂μ := by
        simpa [Zw] using hNorm
      _ = ∫ x, Zw⁻¹ * (w x * (X x - center) ^ 2) ∂μ := by
        rw [integral_const_mul]
      _ = ∫ x, (X x - center) ^ 2 * p x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [p, div_eq_mul_inv]
        ring

  have hEnergyVMeasure :
      (∫ x, (X x - center) ^ 2
          ∂realIntegralWeightedProbabilityMeasure μ v) =
        ∫ x, (X x - center) ^ 2 * q x ∂μ := by
    have hNorm :=
      realIntegralWeightedProbabilityMeasure_integral
        μ v (fun x => (X x - center) ^ 2) hvInt
        (Filter.Eventually.of_forall hv0) hvMassPos
    calc
      (∫ x, (X x - center) ^ 2
          ∂realIntegralWeightedProbabilityMeasure μ v) =
          Zv⁻¹ * ∫ x, v x * (X x - center) ^ 2 ∂μ := by
        simpa [Zv] using hNorm
      _ = ∫ x, Zv⁻¹ * (v x * (X x - center) ^ 2) ∂μ := by
        rw [integral_const_mul]
      _ = ∫ x, (X x - center) ^ 2 * q x ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, div_eq_mul_inv]
        ring

  have hEnergyEq :
      (∫ x, (X x - center) ^ 2 * (p x + q x) ∂μ) =
        (∫ x, (X x - center) ^ 2
            ∂realIntegralWeightedProbabilityMeasure μ w) +
          ∫ x, (X x - center) ^ 2
            ∂realIntegralWeightedProbabilityMeasure μ v := by
    calc
      (∫ x, (X x - center) ^ 2 * (p x + q x) ∂μ) =
          (∫ x, (X x - center) ^ 2 * p x ∂μ) +
            ∫ x, (X x - center) ^ 2 * q x ∂μ := by
        rw [← integral_add hEnergyP hEnergyQ]
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ =
          (∫ x, (X x - center) ^ 2
              ∂realIntegralWeightedProbabilityMeasure μ w) +
            ∫ x, (X x - center) ^ 2
              ∂realIntegralWeightedProbabilityMeasure μ v := by
        rw [hEnergyWMeasure, hEnergyVMeasure]

  rw [hCenteredW, hCenteredV, hDensityCentered]
  rw [hEnergyEq] at hCore
  simpa [K] using hCore

end HaarLikelihoodRatioInfluence

end

end MGAP4D.MathlibAnalytic
