import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- A pointwise relative upper bound between two nonnegative weights transports
to the same relative upper bound between their total masses.  No measurability
hypothesis is needed because `lintegral_const_mul'` only requires the scalar to
be finite. -/
theorem doobWeightMass_le_mul_of_pointwise_le_mul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (R : ℝ≥0∞)
    (hRtop : R ≠ ∞)
    (hwv : ∀ x, w x ≤ R * v x) :
    doobWeightMass μ w ≤ R * doobWeightMass μ v := by
  calc
    doobWeightMass μ w = ∫⁻ x, w x ∂μ := rfl
    _ ≤ ∫⁻ x, R * v x ∂μ := lintegral_mono hwv
    _ = R * ∫⁻ x, v x ∂μ := lintegral_const_mul' R v hRtop
    _ = R * doobWeightMass μ v := rfl

/-- If two weights are mutually pointwise `R`-comparable, normalizing them
costs at most one further factor of `R`.  Thus their normalized Doob densities
are pointwise comparable by `R^2`.

The proof uses only positivity and finiteness of `R`; no nonzero or finiteness
assumption on either total weight mass is required. -/
theorem doobWeightedDensity_le_mul_sq_of_pairwise_le_mul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (R : ℝ≥0∞)
    (hR0 : R ≠ 0)
    (hRtop : R ≠ ∞)
    (hwv : ∀ x, w x ≤ R * v x)
    (hvw : ∀ x, v x ≤ R * w x)
    (x : α) :
    doobWeightedDensity μ w x ≤
      (R * R) * doobWeightedDensity μ v x := by
  have hMassVW :
      doobWeightMass μ v ≤ R * doobWeightMass μ w :=
    doobWeightMass_le_mul_of_pointwise_le_mul μ v w R hRtop hvw
  have hDenom :
      doobWeightMass μ v / R ≤ doobWeightMass μ w :=
    ENNReal.div_le_of_le_mul' hMassVW
  have hRatio :
      w x / doobWeightMass μ w ≤
        (R * v x) / (doobWeightMass μ v / R) :=
    ENNReal.div_le_div (hwv x) hDenom
  change
    w x / doobWeightMass μ w ≤
      (R * R) * (v x / doobWeightMass μ v)
  calc
    w x / doobWeightMass μ w ≤
        (R * v x) / (doobWeightMass μ v / R) := hRatio
    _ = (R * v x) * (doobWeightMass μ v / R)⁻¹ := by
      rw [div_eq_mul_inv]
    _ = (R * v x) * (R / doobWeightMass μ v) := by
      rw [ENNReal.inv_div (Or.inl hRtop) (Or.inl hR0)]
    _ = (R * R) * (v x / doobWeightMass μ v) := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Directional normalized-measure comparison.  Mutual pointwise `R`-control
of two weights on the same reference measure implies that the first normalized
Doob measure is bounded by `R^2` times the second. -/
theorem doobWeightedMeasure_le_mul_sq_of_pairwise_le_mul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (R : ℝ≥0∞)
    (hR0 : R ≠ 0)
    (hRtop : R ≠ ∞)
    (hwv : ∀ x, w x ≤ R * v x)
    (hvw : ∀ x, v x ≤ R * w x) :
    doobWeightedMeasure μ w ≤
      (R * R) • doobWeightedMeasure μ v := by
  have hDensity :
      doobWeightedDensity μ w ≤ᵐ[μ]
        ((R * R) • doobWeightedDensity μ v) := by
    filter_upwards with x
    simpa [Pi.smul_apply, smul_eq_mul] using
      doobWeightedDensity_le_mul_sq_of_pairwise_le_mul
        μ w v R hR0 hRtop hwv hvw x
  have hR2top : R * R ≠ ∞ := ENNReal.mul_ne_top hRtop hRtop
  calc
    doobWeightedMeasure μ w =
        μ.withDensity (doobWeightedDensity μ w) := rfl
    _ ≤ μ.withDensity ((R * R) • doobWeightedDensity μ v) :=
      withDensity_mono hDensity
    _ = (R * R) • μ.withDensity (doobWeightedDensity μ v) :=
      withDensity_smul' (μ := μ) (R * R) (doobWeightedDensity μ v) hR2top
    _ = (R * R) • doobWeightedMeasure μ v := rfl

/-- Symmetric normalized-measure Harnack comparison for mutually pointwise
`R`-comparable weights on a common reference law. -/
theorem doobWeightedMeasure_pairwise_le_mul_sq_of_pointwise_le_mul
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (R : ℝ≥0∞)
    (hR0 : R ≠ 0)
    (hRtop : R ≠ ∞)
    (hwv : ∀ x, w x ≤ R * v x)
    (hvw : ∀ x, v x ≤ R * w x) :
    doobWeightedMeasure μ w ≤
        (R * R) • doobWeightedMeasure μ v ∧
      doobWeightedMeasure μ v ≤
        (R * R) • doobWeightedMeasure μ w := by
  constructor
  · exact doobWeightedMeasure_le_mul_sq_of_pairwise_le_mul
      μ w v R hR0 hRtop hwv hvw
  · exact doobWeightedMeasure_le_mul_sq_of_pairwise_le_mul
      μ v w R hR0 hRtop hvw hwv

end

end MathlibAnalytic
end MGAP4D
