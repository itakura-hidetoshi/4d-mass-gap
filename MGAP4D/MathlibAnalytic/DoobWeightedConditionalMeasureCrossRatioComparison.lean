import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasurePairwiseComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Integrating a pointwise cross-ratio inequality in its second variable
transports it to the corresponding inequality between one pointwise weight and
the opposite total mass.

The finiteness assumptions are exactly those needed by
`lintegral_const_mul'`; no probability normalization is used here. -/
theorem doobWeight_mul_mass_le_of_cross_ratio
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (K : ℝ≥0∞)
    (hKtop : K ≠ ∞)
    (hwtop : ∀ x, w x ≠ ∞)
    (hvtop : ∀ x, v x ≠ ∞)
    (hcross : ∀ x y, w x * v y ≤ K * v x * w y)
    (x : α) :
    w x * doobWeightMass μ v ≤
      (K * v x) * doobWeightMass μ w := by
  calc
    w x * doobWeightMass μ v =
        w x * (∫⁻ y, v y ∂μ) := rfl
    _ = ∫⁻ y, w x * v y ∂μ := by
      symm
      exact lintegral_const_mul' (w x) v (hwtop x)
    _ ≤ ∫⁻ y, (K * v x) * w y ∂μ :=
      lintegral_mono (fun y => hcross x y)
    _ = (K * v x) * (∫⁻ y, w y ∂μ) :=
      lintegral_const_mul' (K * v x) w
        (ENNReal.mul_ne_top hKtop (hvtop x))
    _ = (K * v x) * doobWeightMass μ w := rfl

/-- A cross-ratio bound compares normalized Doob densities with the *same*
constant `K`, rather than paying a second normalization factor.

The hypothesis
`w x * v y ≤ K * v x * w y`
is the multiplicative oscillation condition naturally invariant under separate
rescaling of `w` and `v`.  Thus this theorem exposes normalization cancellation
at the correct level. -/
theorem doobWeightedDensity_le_mul_of_cross_ratio
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (K : ℝ≥0∞)
    (hKtop : K ≠ ∞)
    (hwtop : ∀ x, w x ≠ ∞)
    (hvtop : ∀ x, v x ≠ ∞)
    (hMassW0 : doobWeightMass μ w ≠ 0)
    (hMassWtop : doobWeightMass μ w ≠ ∞)
    (hMassV0 : doobWeightMass μ v ≠ 0)
    (hMassVtop : doobWeightMass μ v ≠ ∞)
    (hcross : ∀ x y, w x * v y ≤ K * v x * w y)
    (x : α) :
    doobWeightedDensity μ w x ≤
      K * doobWeightedDensity μ v x := by
  have hCrossMass :=
    doobWeight_mul_mass_le_of_cross_ratio
      μ w v K hKtop hwtop hvtop hcross x
  have hScaled :=
    mul_le_mul_right' hCrossMass
      ((doobWeightMass μ w)⁻¹ * (doobWeightMass μ v)⁻¹)
  have hWcancel :
      doobWeightMass μ w * (doobWeightMass μ w)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hMassW0 hMassWtop
  have hVcancel :
      doobWeightMass μ v * (doobWeightMass μ v)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hMassV0 hMassVtop
  unfold doobWeightedDensity
  simp only [div_eq_mul_inv]
  calc
    w x * (doobWeightMass μ w)⁻¹ =
        (w x * doobWeightMass μ v) *
          ((doobWeightMass μ w)⁻¹ * (doobWeightMass μ v)⁻¹) := by
      calc
        w x * (doobWeightMass μ w)⁻¹ =
            (w x * (doobWeightMass μ w)⁻¹) * 1 := by simp
        _ = (w x * (doobWeightMass μ w)⁻¹) *
            (doobWeightMass μ v * (doobWeightMass μ v)⁻¹) := by
              rw [hVcancel]
        _ = (w x * doobWeightMass μ v) *
            ((doobWeightMass μ w)⁻¹ * (doobWeightMass μ v)⁻¹) := by
              ac_rfl
    _ ≤ ((K * v x) * doobWeightMass μ w) *
          ((doobWeightMass μ w)⁻¹ * (doobWeightMass μ v)⁻¹) := hScaled
    _ = (K * v x * (doobWeightMass μ v)⁻¹) *
          (doobWeightMass μ w * (doobWeightMass μ w)⁻¹) := by
      ac_rfl
    _ = K * v x * (doobWeightMass μ v)⁻¹ := by rw [hWcancel]; simp
    _ = K * (v x * (doobWeightMass μ v)⁻¹) := by ac_rfl

/-- Directional normalized-measure comparison from a multiplicative
cross-ratio bound.  Unlike the coarse pointwise-comparison route, the
normalization does not square the coefficient. -/
theorem doobWeightedMeasure_le_mul_of_cross_ratio
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (K : ℝ≥0∞)
    (hKtop : K ≠ ∞)
    (hwtop : ∀ x, w x ≠ ∞)
    (hvtop : ∀ x, v x ≠ ∞)
    (hMassW0 : doobWeightMass μ w ≠ 0)
    (hMassWtop : doobWeightMass μ w ≠ ∞)
    (hMassV0 : doobWeightMass μ v ≠ 0)
    (hMassVtop : doobWeightMass μ v ≠ ∞)
    (hcross : ∀ x y, w x * v y ≤ K * v x * w y) :
    doobWeightedMeasure μ w ≤ K • doobWeightedMeasure μ v := by
  have hDensity :
      doobWeightedDensity μ w ≤ᵐ[μ]
        (K • doobWeightedDensity μ v) := by
    filter_upwards with x
    simpa [Pi.smul_apply, smul_eq_mul] using
      doobWeightedDensity_le_mul_of_cross_ratio
        μ w v K hKtop hwtop hvtop
        hMassW0 hMassWtop hMassV0 hMassVtop hcross x
  calc
    doobWeightedMeasure μ w =
        μ.withDensity (doobWeightedDensity μ w) := rfl
    _ ≤ μ.withDensity (K • doobWeightedDensity μ v) :=
      withDensity_mono hDensity
    _ = K • μ.withDensity (doobWeightedDensity μ v) :=
      withDensity_smul' (μ := μ) K (doobWeightedDensity μ v) hKtop
    _ = K • doobWeightedMeasure μ v := rfl

/-- A single all-pairs cross-ratio bound is symmetric after swapping the two
fiber variables.  Consequently the two normalized Doob measures mutually
dominate each other with exactly the same coefficient `K`.

This is the normalization-aware interface intended for later geometric or
distance-decay estimates: proving a better cross-ratio oscillation bound feeds
through without an additional normalization loss. -/
theorem doobWeightedMeasure_pairwise_le_mul_of_cross_ratio
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w v : α → ℝ≥0∞)
    (K : ℝ≥0∞)
    (hKtop : K ≠ ∞)
    (hwtop : ∀ x, w x ≠ ∞)
    (hvtop : ∀ x, v x ≠ ∞)
    (hMassW0 : doobWeightMass μ w ≠ 0)
    (hMassWtop : doobWeightMass μ w ≠ ∞)
    (hMassV0 : doobWeightMass μ v ≠ 0)
    (hMassVtop : doobWeightMass μ v ≠ ∞)
    (hcross : ∀ x y, w x * v y ≤ K * v x * w y) :
    doobWeightedMeasure μ w ≤ K • doobWeightedMeasure μ v ∧
      doobWeightedMeasure μ v ≤ K • doobWeightedMeasure μ w := by
  constructor
  · exact doobWeightedMeasure_le_mul_of_cross_ratio
      μ w v K hKtop hwtop hvtop
      hMassW0 hMassWtop hMassV0 hMassVtop hcross
  · apply doobWeightedMeasure_le_mul_of_cross_ratio
      μ v w K hKtop hvtop hwtop
      hMassV0 hMassVtop hMassW0 hMassWtop
    intro x y
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcross y x

end

end MathlibAnalytic
end MGAP4D
