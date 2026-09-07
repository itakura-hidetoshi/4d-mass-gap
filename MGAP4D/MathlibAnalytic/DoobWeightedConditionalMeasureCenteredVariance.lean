import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureComparison
import Mathlib.Probability.Moments.Variance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

/-- Extended nonnegative squared residual from a constant center.  This is the
fiberwise `L²` residual whose infimum over centers is the scalar projection
energy onto constants. -/
def doobCenteredSquaredResidual
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (c : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((X x - c) ^ 2) ∂μ

/-- Best squared residual from the constant subspace.  It is defined as an
infimum so that measure comparison can be passed through without choosing a
center in advance. -/
def doobBestConstantSquaredResidual
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) : ℝ≥0∞ :=
  ⨅ c : ℝ, doobCenteredSquaredResidual μ X c

/-- The best constant residual is no larger than the residual at any fixed
center. -/
theorem doobBestConstantSquaredResidual_le_centered
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) (c : ℝ) :
    doobBestConstantSquaredResidual μ X ≤
      doobCenteredSquaredResidual μ X c := by
  exact iInf_le (fun d : ℝ => doobCenteredSquaredResidual μ X d) c

/-- Exact Doob lower comparison for the squared residual at a fixed center. -/
theorem doobWeightedMeasure_centeredSquaredResidual_lower_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (X : α → ℝ)
    (m : ℝ≥0∞) (hLower : ∀ x, m ≤ w x) (c : ℝ) :
    (m / doobWeightMass μ w) * doobCenteredSquaredResidual μ X c ≤
      doobCenteredSquaredResidual (doobWeightedMeasure μ w) X c := by
  simpa [doobCenteredSquaredResidual] using
    doobWeightedMeasure_lintegral_lower_bound_exact
      μ w (fun x => ENNReal.ofReal ((X x - c) ^ 2)) m hLower

/-- Exact Doob lower comparison after minimizing over all constant centers.
No minimizer needs to be selected. -/
theorem doobWeightedMeasure_bestConstantSquaredResidual_lower_bound_exact
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (w : α → ℝ≥0∞) (X : α → ℝ)
    (m : ℝ≥0∞) (hLower : ∀ x, m ≤ w x) :
    (m / doobWeightMass μ w) * doobBestConstantSquaredResidual μ X ≤
      doobBestConstantSquaredResidual (doobWeightedMeasure μ w) X := by
  refine le_iInf fun c => ?_
  calc
    (m / doobWeightMass μ w) * doobBestConstantSquaredResidual μ X ≤
        (m / doobWeightMass μ w) * doobCenteredSquaredResidual μ X c :=
      mul_le_mul_left'
        (doobBestConstantSquaredResidual_le_centered μ X c)
        (m / doobWeightMass μ w)
    _ ≤ doobCenteredSquaredResidual (doobWeightedMeasure μ w) X c :=
      doobWeightedMeasure_centeredSquaredResidual_lower_bound_exact
        μ w X m hLower c

/-- Coarse Doob lower comparison at a fixed center using only the density
oscillation ratio `m / M`. -/
theorem doobWeightedMeasure_centeredSquaredResidual_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (X : α → ℝ) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) (c : ℝ) :
    (m / M) * doobCenteredSquaredResidual μ X c ≤
      doobCenteredSquaredResidual (doobWeightedMeasure μ w) X c := by
  simpa [doobCenteredSquaredResidual] using
    doobWeightedMeasure_lintegral_lower_bound
      μ w (fun x => ENNReal.ofReal ((X x - c) ^ 2)) m M hLower hUpper

/-- Coarse lower comparison for the best constant residual.  This is the
measure-theoretic core of the variance/Poincaré transfer: a Doob distortion
bounded between `m` and `M` loses at most the factor `m / M`. -/
theorem doobWeightedMeasure_bestConstantSquaredResidual_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (X : α → ℝ) (m M : ℝ≥0∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M) :
    (m / M) * doobBestConstantSquaredResidual μ X ≤
      doobBestConstantSquaredResidual (doobWeightedMeasure μ w) X := by
  refine le_iInf fun c => ?_
  calc
    (m / M) * doobBestConstantSquaredResidual μ X ≤
        (m / M) * doobCenteredSquaredResidual μ X c :=
      mul_le_mul_left'
        (doobBestConstantSquaredResidual_le_centered μ X c) (m / M)
    _ ≤ doobCenteredSquaredResidual (doobWeightedMeasure μ w) X c :=
      doobWeightedMeasure_centeredSquaredResidual_lower_bound
        μ w X m M hLower hUpper c

/-- The best constant squared residual is always bounded above by Mathlib's
extended variance, since the expectation is one admissible center. -/
theorem doobBestConstantSquaredResidual_le_evariance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (X : α → ℝ) :
    doobBestConstantSquaredResidual μ X ≤ evariance X μ := by
  rw [evariance_eq_lintegral_ofReal]
  simpa [doobCenteredSquaredResidual] using
    (doobBestConstantSquaredResidual_le_centered
      μ X (∫ x, X x ∂μ))

/-- For a square-integrable random variable on a probability space, Mathlib's
extended variance is no larger than the squared residual at any constant
center. -/
theorem evariance_le_doobCenteredSquaredResidual
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    evariance X μ ≤ doobCenteredSquaredResidual μ X c := by
  have hShift : MemLp (fun x => X x - c) 2 μ :=
    hX.sub (memLp_const c)
  have hSqIntegrable : Integrable (fun x => (X x - c) ^ 2) μ := by
    simpa only [Pi.pow_apply] using hShift.integrable_sq
  have hReal : variance X μ ≤ ∫ x, (X x - c) ^ 2 ∂μ := by
    calc
      variance X μ = variance (fun x => X x - c) μ :=
        (variance_sub_const hX.aestronglyMeasurable c).symm
      _ ≤ ∫ x, (X x - c) ^ 2 ∂μ := by
        simpa only [Pi.pow_apply] using
          (variance_le_expectation_sq
            (μ := μ) (X := fun x => X x - c)
            hShift.aestronglyMeasurable)
  rw [← hX.ofReal_variance_eq]
  rw [doobCenteredSquaredResidual,
    ← ofReal_integral_eq_lintegral_ofReal hSqIntegrable
      (ae_of_all μ fun x => sq_nonneg (X x - c))]
  exact ENNReal.ofReal_le_ofReal hReal

/-- On a probability space, the best constant squared residual agrees exactly
with Mathlib's extended variance for every `L²` random variable. -/
theorem doobBestConstantSquaredResidual_eq_evariance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) :
    doobBestConstantSquaredResidual μ X = evariance X μ := by
  apply le_antisymm
  · exact doobBestConstantSquaredResidual_le_evariance μ X
  · refine le_iInf fun c => ?_
    exact evariance_le_doobCenteredSquaredResidual μ X hX c

/-- Quantitative variance transfer through a normalized Doob reweighting.
Under positive finite two-sided density bounds, an `L²` variable on the raw
probability space remains `L²` after reweighting, and its extended variance
loses at most the sharp density-distortion factor `m / M`. -/
theorem doobWeightedMeasure_evariance_lower_bound
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (w : α → ℝ≥0∞) (X : α → ℝ) (m M : ℝ≥0∞)
    (hw : AEMeasurable w μ)
    (hm : 0 < m) (hM : M < ∞)
    (hLower : ∀ x, m ≤ w x)
    (hUpper : ∀ x, w x ≤ M)
    (hX : MemLp X 2 μ) :
    (m / M) * evariance X μ ≤
      evariance X (doobWeightedMeasure μ w) := by
  letI : IsProbabilityMeasure (doobWeightedMeasure μ w) :=
    doobWeightedMeasure_isProbabilityMeasure_of_bounds
      μ w m M hw hm hM hLower hUpper
  have hRatioTop : M / m ≠ ∞ :=
    ENNReal.div_ne_top (ne_of_lt hM) (ne_of_gt hm)
  have hXWeighted : MemLp X 2 (doobWeightedMeasure μ w) :=
    (hX.smul_measure hRatioTop).mono_measure
      (doobWeightedMeasure_upper_bound μ w m M hLower hUpper)
  calc
    (m / M) * evariance X μ =
        (m / M) * doobBestConstantSquaredResidual μ X := by
      rw [doobBestConstantSquaredResidual_eq_evariance μ X hX]
    _ ≤ doobBestConstantSquaredResidual (doobWeightedMeasure μ w) X :=
      doobWeightedMeasure_bestConstantSquaredResidual_lower_bound
        μ w X m M hLower hUpper
    _ = evariance X (doobWeightedMeasure μ w) :=
      doobBestConstantSquaredResidual_eq_evariance
        (doobWeightedMeasure μ w) X hXWeighted

end

end MathlibAnalytic
end MGAP4D
