import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureNormalizationIdentity
import MGAP4D.MathlibAnalytic.RealIntegralCrossRatioCovarianceLocalization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Normalize a nonnegative real weight by reusing the canonical ENNReal
`doobWeightedMeasure` construction.  The definition itself is total; the
probability theorem below records the exact positivity/finiteness obligations. -/
def realIntegralWeightedProbabilityMeasure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ℝ) : Measure α :=
  doobWeightedMeasure μ (fun x => ENNReal.ofReal (w x))

/-- Ordinary real covariance under an arbitrary reference measure.  This is
kept independent of probability normalization so the algebraic normalization
identity can be stated without hiding its mass factor. -/
def realIntegralCovariance
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α)
    (f g : α → ℝ) : ℝ :=
  (∫ x, f x * g x ∂ν) - (∫ x, f x ∂ν) * (∫ x, g x ∂ν)

/-- For an integrable nonnegative real weight, the ENNReal Doob mass is exactly
the `ofReal` image of its ordinary real integral. -/
theorem realIntegralWeighted_doobWeightMass_eq_ofReal_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ℝ)
    (hwInt : Integrable w μ)
    (hwNonneg : ∀ᵐ x ∂μ, 0 ≤ w x) :
    doobWeightMass μ (fun x => ENNReal.ofReal (w x)) =
      ENNReal.ofReal (∫ x, w x ∂μ) := by
  unfold doobWeightMass
  exact (ofReal_integral_eq_lintegral_ofReal hwInt hwNonneg).symm

/-- Positive real mass supplies the nonzero and finite ENNReal normalization
receipts needed by `doobWeightedMeasure`. -/
theorem realIntegralWeightedProbabilityMeasure_isProbabilityMeasure
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w : α → ℝ)
    (hwInt : Integrable w μ)
    (hwNonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hMassPos : 0 < ∫ x, w x ∂μ) :
    IsProbabilityMeasure (realIntegralWeightedProbabilityMeasure μ w) := by
  let rho : α → ENNReal := fun x => ENNReal.ofReal (w x)
  have hwAE : AEMeasurable w μ :=
    hwInt.aestronglyMeasurable.aemeasurable
  have hrhoAE : AEMeasurable rho μ := by
    simpa [rho, Function.comp_def] using
      ENNReal.measurable_ofReal.comp_aemeasurable hwAE
  have hMassEq :
      doobWeightMass μ rho = ENNReal.ofReal (∫ x, w x ∂μ) := by
    simpa [rho] using
      realIntegralWeighted_doobWeightMass_eq_ofReal_integral μ w hwInt hwNonneg
  have hMassZero : doobWeightMass μ rho ≠ 0 := by
    rw [hMassEq]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr hMassPos)
  have hMassTop : doobWeightMass μ rho ≠ ∞ := by
    rw [hMassEq]
    exact ne_of_lt ENNReal.ofReal_lt_top
  refine ⟨?_⟩
  simpa [realIntegralWeightedProbabilityMeasure, rho] using
    doobWeightedMeasure_measure_univ μ rho hrhoAE hMassZero hMassTop

/-- Exact expectation normalization for an integrable nonnegative real weight.
The observable is not given an artificial integrability hypothesis: the
with-density integral formula itself determines the normalized expectation. -/
theorem realIntegralWeightedProbabilityMeasure_integral
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w f : α → ℝ)
    (hwInt : Integrable w μ)
    (hwNonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hMassPos : 0 < ∫ x, w x ∂μ) :
    (∫ x, f x ∂realIntegralWeightedProbabilityMeasure μ w) =
      (∫ x, w x ∂μ)⁻¹ * ∫ x, w x * f x ∂μ := by
  rfl

end

end MathlibAnalytic
end MGAP4D
