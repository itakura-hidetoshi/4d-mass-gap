import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- Total mass of a nonnegative weight relative to a reference measure. -/
def doobWeightMass {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x, w x ∂μ

/-- The normalized Doob density `w / ∫ w dμ`.  The normalization is deliberately
kept as an `ℝ≥0∞` quantity so that comparison constants remain exact before
any finiteness specialization. -/
def doobWeightedDensity {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (x : α) : ℝ≥0∞ :=
  w x / doobWeightMass μ w

/-- Probability candidate obtained by normalizing a nonnegative density with
respect to a reference measure. -/
def doobWeightedMeasure {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) : Measure α :=
  μ.withDensity (doobWeightedDensity μ w)

/-- A pointwise lower bound on a weight gives the same lower bound on its total
mass over a probability measure. -/
theorem doobWeightMass_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (m : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x) :
    m ≤ doobWeightMass μ w := by
  calc
    m = ∫⁻ _ : α, m ∂μ := by simp
    _ ≤ ∫⁻ x, w x ∂μ := lintegral_mono hLower
    _ = doobWeightMass μ w := rfl

/-- A pointwise upper bound on a weight gives the same upper bound on its total
mass over a probability measure. -/
theorem doobWeightMass_upper_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (M : ℝ≥0∞)
    (hUpper : ∀ x, w x ≤ M) :
    doobWeightMass μ w ≤ M := by
  calc
    doobWeightMass μ w = ∫⁻ x, w x ∂μ := rfl
    _ ≤ ∫⁻ _ : α, M ∂μ := lintegral_mono hUpper
    _ = M := by simp

/-- Exact lower density comparison before replacing the normalization by a
coarse upper bound. -/
theorem doobWeightedDensity_lower_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (m : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x) (x : α) :
    m / doobWeightMass μ w ≤ doobWeightedDensity μ w x := by
  exact ENNReal.div_le_div_right (hLower x) (doobWeightMass μ w)

/-- Exact upper density comparison before replacing the normalization by a
coarse lower bound. -/
theorem doobWeightedDensity_upper_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (M : ℝ≥0∞)
    (hUpper : ∀ x, w x ≤ M) (x : α) :
    doobWeightedDensity μ w x ≤ M / doobWeightMass μ w := by
  exact ENNReal.div_le_div_right (hUpper x) (doobWeightMass μ w)

/-- Exact lower comparison of the Doob-weighted measure with its reference
measure. -/
theorem doobWeightedMeasure_lower_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (m : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x) :
    (m / doobWeightMass μ w) • μ ≤ doobWeightedMeasure μ w := by
  have hDensity :
      (fun _ : α => m / doobWeightMass μ w) ≤ᵐ[μ]
        doobWeightedDensity μ w :=
    ae_of_all μ (fun x =>
      doobWeightedDensity_lower_bound_exact μ w m hLower x)
  simpa [doobWeightedMeasure] using
    (withDensity_mono (μ := μ) hDensity)

/-- Exact upper comparison of the Doob-weighted measure with its reference
measure. -/
theorem doobWeightedMeasure_upper_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (M : ℝ≥0∞)
    (hUpper : ∀ x, w x ≤ M) :
    doobWeightedMeasure μ w ≤ (M / doobWeightMass μ w) • μ := by
  have hDensity :
      doobWeightedDensity μ w ≤ᵐ[μ]
        (fun _ : α => M / doobWeightMass μ w) :=
    ae_of_all μ (fun x =>
      doobWeightedDensity_upper_bound_exact μ w M hUpper x)
  simpa [doobWeightedMeasure] using
    (withDensity_mono (μ := μ) hDensity)

/-- On a probability reference measure, two-sided pointwise bounds on the
weight give the familiar lower distortion coefficient `m / M`. -/
theorem doobWeightedDensity_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) (x : α) :
    m / M ≤ doobWeightedDensity μ w x := by
  exact ENNReal.div_le_div (hLower x)
    (doobWeightMass_upper_bound μ w M hUpper)

/-- On a probability reference measure, two-sided pointwise bounds on the
weight give the corresponding upper distortion coefficient `M / m`. -/
theorem doobWeightedDensity_upper_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) (x : α) :
    doobWeightedDensity μ w x ≤ M / m := by
  exact ENNReal.div_le_div (hUpper x)
    (doobWeightMass_lower_bound μ w m hLower)

/-- Coarse lower measure comparison using only the pointwise ratio `m / M`. -/
theorem doobWeightedMeasure_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    (m / M) • μ ≤ doobWeightedMeasure μ w := by
  have hDensity :
      (fun _ : α => m / M) ≤ᵐ[μ] doobWeightedDensity μ w :=
    ae_of_all μ (fun x =>
      doobWeightedDensity_lower_bound μ w m M hLower hUpper x)
  simpa [doobWeightedMeasure] using
    (withDensity_mono (μ := μ) hDensity)

/-- Coarse upper measure comparison using only the pointwise ratio `M / m`. -/
theorem doobWeightedMeasure_upper_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    doobWeightedMeasure μ w ≤ (M / m) • μ := by
  have hDensity :
      doobWeightedDensity μ w ≤ᵐ[μ] (fun _ : α => M / m) :=
    ae_of_all μ (fun x =>
      doobWeightedDensity_upper_bound μ w m M hLower hUpper x)
  simpa [doobWeightedMeasure] using
    (withDensity_mono (μ := μ) hDensity)

/-- If the normalization is nonzero and finite, the normalized Doob measure
has total mass one. -/
theorem doobWeightedMeasure_measure_univ
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞)
    (hw : AEMeasurable w μ)
    (hMassZero : doobWeightMass μ w ≠ 0)
    (hMassTop : doobWeightMass μ w ≠ ∞) :
    doobWeightedMeasure μ w Set.univ = 1 := by
  rw [doobWeightedMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  change ∫⁻ x, w x / doobWeightMass μ w ∂μ = 1
  simp only [div_eq_mul_inv]
  rw [lintegral_mul_const'' _ hw]
  exact ENNReal.mul_inv_cancel hMassZero hMassTop

/-- A positive lower bound and finite upper bound automatically make the
normalized Doob measure a probability measure. -/
theorem doobWeightedMeasure_isProbabilityMeasure_of_bounds
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hw : AEMeasurable w μ)
    (hm : 0 < m) (hM : M < ∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    IsProbabilityMeasure (doobWeightedMeasure μ w) := by
  have hMassLower : m ≤ doobWeightMass μ w :=
    doobWeightMass_lower_bound μ w m hLower
  have hMassUpper : doobWeightMass μ w ≤ M :=
    doobWeightMass_upper_bound μ w M hUpper
  refine ⟨doobWeightedMeasure_measure_univ μ w hw ?_ ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le hm hMassLower)
  · exact ne_of_lt (lt_of_le_of_lt hMassUpper hM)

/-- Exact lower comparison for every nonnegative energy observable.  This is
the form used later with squared conditional-expectation residuals. -/
theorem doobWeightedMeasure_lintegral_lower_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w g : α → ℝ≥0∞) (m : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x) :
    (m / doobWeightMass μ w) * (∫⁻ x, g x ∂μ) ≤
      ∫⁻ x, g x ∂doobWeightedMeasure μ w := by
  calc
    (m / doobWeightMass μ w) * (∫⁻ x, g x ∂μ) =
        ∫⁻ x, g x ∂((m / doobWeightMass μ w) • μ) := by
      simpa [smul_eq_mul] using
        (lintegral_smul_measure (μ := μ)
          (m / doobWeightMass μ w) g).symm
    _ ≤ ∫⁻ x, g x ∂doobWeightedMeasure μ w :=
      lintegral_mono' (doobWeightedMeasure_lower_bound_exact μ w m hLower) le_rfl

/-- Exact upper comparison for every nonnegative energy observable. -/
theorem doobWeightedMeasure_lintegral_upper_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w g : α → ℝ≥0∞) (M : ℝ≥0∞)
    (hUpper : ∀ x, w x ≤ M) :
    (∫⁻ x, g x ∂doobWeightedMeasure μ w) ≤
      (M / doobWeightMass μ w) * (∫⁻ x, g x ∂μ) := by
  calc
    (∫⁻ x, g x ∂doobWeightedMeasure μ w) ≤
        ∫⁻ x, g x ∂((M / doobWeightMass μ w) • μ) :=
      lintegral_mono' (doobWeightedMeasure_upper_bound_exact μ w M hUpper) le_rfl
    _ = (M / doobWeightMass μ w) * (∫⁻ x, g x ∂μ) := by
      simpa [smul_eq_mul] using
        (lintegral_smul_measure (μ := μ)
          (M / doobWeightMass μ w) g)

/-- Coarse lower `L²`-energy comparison with the normalization eliminated.
The observable is arbitrary and nonnegative, so the theorem applies directly
to squared residuals. -/
theorem doobWeightedMeasure_lintegral_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w g : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    (m / M) * (∫⁻ x, g x ∂μ) ≤
      ∫⁻ x, g x ∂doobWeightedMeasure μ w := by
  calc
    (m / M) * (∫⁻ x, g x ∂μ) =
        ∫⁻ x, g x ∂((m / M) • μ) := by
      simpa [smul_eq_mul] using
        (lintegral_smul_measure (μ := μ) (m / M) g).symm
    _ ≤ ∫⁻ x, g x ∂doobWeightedMeasure μ w :=
      lintegral_mono' (doobWeightedMeasure_lower_bound μ w m M hLower hUpper) le_rfl

/-- Coarse upper `L²`-energy comparison with the normalization eliminated. -/
theorem doobWeightedMeasure_lintegral_upper_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w g : α → ℝ≥0∞) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    (∫⁻ x, g x ∂doobWeightedMeasure μ w) ≤
      (M / m) * (∫⁻ x, g x ∂μ) := by
  calc
    (∫⁻ x, g x ∂doobWeightedMeasure μ w) ≤
        ∫⁻ x, g x ∂((M / m) • μ) :=
      lintegral_mono' (doobWeightedMeasure_upper_bound μ w m M hLower hUpper) le_rfl
    _ = (M / m) * (∫⁻ x, g x ∂μ) := by
      simpa [smul_eq_mul] using
        (lintegral_smul_measure (μ := μ) (M / m) g)

end

end MathlibAnalytic
end MGAP4D
