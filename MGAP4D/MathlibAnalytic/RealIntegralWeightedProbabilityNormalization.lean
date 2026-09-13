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
  let rho : α → ENNReal := fun x => ENNReal.ofReal (w x)
  let mass : ENNReal := doobWeightMass μ rho
  let Z : ℝ := ∫ x, w x ∂μ
  have hwAE : AEMeasurable w μ :=
    hwInt.aestronglyMeasurable.aemeasurable
  have hrhoAE : AEMeasurable rho μ := by
    simpa [rho, Function.comp_def] using
      ENNReal.measurable_ofReal.comp_aemeasurable hwAE
  have hMassEq : mass = ENNReal.ofReal Z := by
    simpa [mass, rho, Z] using
      realIntegralWeighted_doobWeightMass_eq_ofReal_integral μ w hwInt hwNonneg
  have hMassZero : mass ≠ 0 := by
    rw [hMassEq]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by simpa [Z] using hMassPos))
  have hDensityTop :
      ∀ᵐ x ∂μ, rho x / mass < ∞ := by
    filter_upwards with x
    exact ENNReal.div_lt_top (ne_of_lt ENNReal.ofReal_lt_top) hMassZero
  change
    (∫ x, f x ∂μ.withDensity (fun x => rho x / mass)) =
      Z⁻¹ * ∫ x, w x * f x ∂μ
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (hrhoAE.div_const mass) hDensityTop f]
  calc
    (∫ x, (rho x / mass).toReal • f x ∂μ) =
        ∫ x, Z⁻¹ * (w x * f x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hwNonneg] with x hx
      rw [ENNReal.toReal_div, hMassEq]
      rw [ENNReal.toReal_ofReal hx,
        ENNReal.toReal_ofReal (by simpa [Z] using hMassPos.le)]
      simp only [smul_eq_mul]
      field_simp [show Z ≠ 0 by exact ne_of_gt (by simpa [Z] using hMassPos)]
      <;> ring
    _ = Z⁻¹ * ∫ x, w x * f x ∂μ := by
      rw [integral_const_mul]
    _ = (∫ x, w x ∂μ)⁻¹ * ∫ x, w x * f x ∂μ := by
      rfl

/-- Unnormalized weighted covariance is exactly total-mass squared times the
ordinary covariance under the normalized weighted probability law. -/
theorem realIntegralWeightedCovarianceNumerator_eq_mass_sq_mul_probabilityCovariance
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α)
    (w f g : α → ℝ)
    (hwInt : Integrable w μ)
    (hwNonneg : ∀ᵐ x ∂μ, 0 ≤ w x)
    (hMassPos : 0 < ∫ x, w x ∂μ) :
    realIntegralWeightedCovarianceNumerator μ w f g =
      (∫ x, w x ∂μ) ^ 2 *
        realIntegralCovariance
          (realIntegralWeightedProbabilityMeasure μ w) f g := by
  have hJoint :=
    realIntegralWeightedProbabilityMeasure_integral
      μ w (fun x => f x * g x) hwInt hwNonneg hMassPos
  have hLeft :=
    realIntegralWeightedProbabilityMeasure_integral
      μ w f hwInt hwNonneg hMassPos
  have hRight :=
    realIntegralWeightedProbabilityMeasure_integral
      μ w g hwInt hwNonneg hMassPos
  unfold realIntegralWeightedCovarianceNumerator realIntegralCovariance
  rw [hJoint, hLeft, hRight]
  field_simp [ne_of_gt hMassPos]
  <;> ring

end

end MathlibAnalytic
end MGAP4D
