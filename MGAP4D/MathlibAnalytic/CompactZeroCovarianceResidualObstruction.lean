import MGAP4D.MathlibAnalytic.CompactEnergyMismatchMoment
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Positive residual variance at zero covariance

A continuous covariance can vanish where the continuous variance is positive.
At such a point the residual `V - 4 * C²` equals `V`. Every finite covariance
square cap therefore fails on a nonempty open set. A measure positive on
nonempty open sets assigns positive measure to that violation set, so the cap
cannot hold almost everywhere.

The same witness excludes every variance cap with coefficient strictly below
one. Compact probability spaces with full support are included, but neither
compactness nor probability normalization is needed for this local argument.
The physical specialization must supply its actual measure, continuous
functions, and a positive-variance zero-covariance witness.
-/

namespace MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction

open MeasureTheory

noncomputable section
set_option autoImplicit false

variable {α : Type*}

/-- A positive-variance zero-covariance point rules out every all-context
covariance-square cap, for any real coefficient. -/
theorem not_allContext_cap (V C : α → ℝ) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (K : ℝ) :
    ¬ (∀ z : α, V z - 4 * (C z) ^ 2 ≤ K * (C z) ^ 2) := by
  intro hCap
  have hz : V z0 ≤ 0 := by
    simpa [hC0] using hCap z0
  exact (not_le_of_gt hV0) hz

/-- There is no finite real coefficient giving an all-context
covariance-square cap. -/
theorem not_exists_allContext_cap (V C : α → ℝ) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) :
    ¬ (∃ K : ℝ, ∀ z : α, V z - 4 * (C z) ^ 2 ≤ K * (C z) ^ 2) := by
  rintro ⟨K, hCap⟩
  exact not_allContext_cap V C z0 hV0 hC0 K hCap

/-- The same point excludes every all-context variance cap below one. -/
theorem not_allContext_variance_cap (V C : α → ℝ) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (theta : ℝ) (htheta : theta < 1) :
    ¬ (∀ z : α, V z - 4 * (C z) ^ 2 ≤ theta * V z) := by
  intro hCap
  have hz : V z0 ≤ theta * V z0 := by
    simpa [hC0] using hCap z0
  have hStrict : theta * V z0 < V z0 := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta hV0
  exact (not_le_of_gt hStrict) hz

section Topological

variable [TopologicalSpace α]

/-- Strict failure of a finite covariance-square cap is open. -/
theorem strictViolation_isOpen (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (K : ℝ) :
    IsOpen {z : α | K * (C z) ^ 2 < V z - 4 * (C z) ^ 2} := by
  exact isOpen_lt (continuous_const.mul (hC.pow 2))
    (hV.sub (continuous_const.mul (hC.pow 2)))

/-- Strict failure remains open when a positive variance amplitude is retained. -/
theorem positiveAmplitudeViolation_isOpen (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (v K : ℝ) :
    IsOpen {z : α | v < V z ∧ K * (C z) ^ 2 < V z - 4 * (C z) ^ 2} := by
  exact (isOpen_lt continuous_const hV).inter
    (strictViolation_isOpen V C hV hC K)

/-- Strict failure of a variance cap is open. -/
theorem varianceStrictViolation_isOpen (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (theta : ℝ) :
    IsOpen {z : α | theta * V z < V z - 4 * (C z) ^ 2} := by
  exact isOpen_lt (continuous_const.mul hV)
    (hV.sub (continuous_const.mul (hC.pow 2)))

section Measure

variable [MeasurableSpace α] (μ : Measure α) [Measure.IsOpenPosMeasure μ]

/-- Every finite covariance-square cap fails on a set of positive measure. -/
theorem strictViolation_measure_pos (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (K : ℝ) :
    0 < μ {z : α | K * (C z) ^ 2 < V z - 4 * (C z) ^ 2} := by
  apply (strictViolation_isOpen V C hV hC K).measure_pos μ
  refine ⟨z0, ?_⟩
  simpa [hC0] using hV0

/-- The positive-measure violation can retain at least half the witness variance.
This supplies an explicit local amplitude, without a global quantitative floor. -/
theorem positiveAmplitudeViolation_measure_pos (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (K : ℝ) :
    0 < μ {z : α | V z0 / 2 < V z ∧
      K * (C z) ^ 2 < V z - 4 * (C z) ^ 2} := by
  apply (positiveAmplitudeViolation_isOpen V C hV hC (V z0 / 2) K).measure_pos μ
  refine ⟨z0, ?_⟩
  constructor
  · linarith
  · simpa [hC0] using hV0

/-- A finite covariance-square cap cannot hold almost everywhere. -/
theorem not_ae_cap (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (K : ℝ) :
    ¬ (∀ᵐ z ∂μ, V z - 4 * (C z) ^ 2 ≤ K * (C z) ^ 2) := by
  intro hCap
  have hNull : μ {z : α | K * (C z) ^ 2 < V z - 4 * (C z) ^ 2} = 0 := by
    simpa only [not_le] using (ae_iff.mp hCap)
  exact (strictViolation_measure_pos μ V C hV hC z0 hV0 hC0 K).ne' hNull

/-- There is no finite real coefficient giving an almost-everywhere
covariance-square cap. -/
theorem not_exists_ae_cap (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) :
    ¬ (∃ K : ℝ, ∀ᵐ z ∂μ, V z - 4 * (C z) ^ 2 ≤ K * (C z) ^ 2) := by
  rintro ⟨K, hCap⟩
  exact not_ae_cap μ V C hV hC z0 hV0 hC0 K hCap

/-- Every variance cap below one fails on a set of positive measure. -/
theorem varianceStrictViolation_measure_pos (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (theta : ℝ) (htheta : theta < 1) :
    0 < μ {z : α | theta * V z < V z - 4 * (C z) ^ 2} := by
  apply (varianceStrictViolation_isOpen V C hV hC theta).measure_pos μ
  refine ⟨z0, ?_⟩
  have hStrict : theta * V z0 < V z0 := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right htheta hV0
  simpa [hC0] using hStrict

/-- A variance cap with coefficient strictly below one cannot hold almost
everywhere under the same original measure. -/
theorem not_ae_variance_cap (V C : α → ℝ)
    (hV : Continuous V) (hC : Continuous C) (z0 : α)
    (hV0 : 0 < V z0) (hC0 : C z0 = 0) (theta : ℝ) (htheta : theta < 1) :
    ¬ (∀ᵐ z ∂μ, V z - 4 * (C z) ^ 2 ≤ theta * V z) := by
  intro hCap
  have hNull : μ {z : α | theta * V z < V z - 4 * (C z) ^ 2} = 0 := by
    simpa only [not_le] using (ae_iff.mp hCap)
  exact (varianceStrictViolation_measure_pos μ V C hV hC z0 hV0 hC0 theta htheta).ne'
    hNull

end Measure
end Topological

end

end MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction

#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.not_allContext_cap
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.not_exists_allContext_cap
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.not_allContext_variance_cap
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.strictViolation_isOpen
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.positiveAmplitudeViolation_isOpen
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.varianceStrictViolation_isOpen
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.strictViolation_measure_pos
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.positiveAmplitudeViolation_measure_pos
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.not_ae_cap
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.not_exists_ae_cap
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.varianceStrictViolation_measure_pos
#print axioms MGAP4D.MathlibAnalytic.CompactZeroCovarianceResidualObstruction.not_ae_variance_cap

