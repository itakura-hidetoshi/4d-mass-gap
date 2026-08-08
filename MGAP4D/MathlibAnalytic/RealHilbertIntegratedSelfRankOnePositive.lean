import MGAP4D.MathlibAnalytic.RealHilbertIntegratedSelfRankOne
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {H : Type v}
  [MeasurableSpace α]
  [NormedAddCommGroup H]
  [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- Every real-Hilbert self rank-one operator is symmetric. -/
theorem realHilbertSelfRankOne_isSymmetric (v : H) :
    ((realHilbertSelfRankOne v : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
  rw [realHilbertSelfRankOne_eq_rankOne]
  exact InnerProductSpace.isSymmetric_rankOne_self v

/-- Exact bilinear form of the integrated self-rank-one operator. -/
theorem realHilbertIntegratedSelfRankOne_inner
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ)
    (x y : H) :
    inner ℝ (realHilbertIntegratedSelfRankOne μ v x) y =
      ∫ a, inner ℝ (v a) x * inner ℝ (v a) y ∂μ := by
  have hOp : Integrable (fun a => realHilbertSelfRankOne (v a)) μ :=
    realHilbertSelfRankOne_integrable hv hv2
  have hxInt : Integrable (fun a => realHilbertSelfRankOne (v a) x) μ :=
    (ContinuousLinearMap.apply ℝ H x).integrable_comp hOp
  rw [realHilbertIntegratedSelfRankOne,
    ContinuousLinearMap.integral_apply hOp x,
    real_inner_comm,
    ← integral_inner hxInt y]
  apply integral_congr_ae
  filter_upwards with a
  simp [realHilbertSelfRankOne_apply, real_inner_comm, mul_comm]

/-- The integrated feature operator is symmetric. -/
theorem realHilbertIntegratedSelfRankOne_isSymmetric
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ) :
    ((realHilbertIntegratedSelfRankOne μ v : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric := by
  intro x y
  rw [realHilbertIntegratedSelfRankOne_inner hv hv2 x y,
    realHilbertIntegratedSelfRankOne_inner hv hv2 y x]
  apply integral_congr_ae
  filter_upwards with a
  ring

/-- The quadratic form of the integrated feature operator is the integral of
squares of scalar feature coefficients. -/
theorem realHilbertIntegratedSelfRankOne_inner_self
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ)
    (x : H) :
    inner ℝ (realHilbertIntegratedSelfRankOne μ v x) x =
      ∫ a, (inner ℝ (v a) x) ^ 2 ∂μ := by
  rw [realHilbertIntegratedSelfRankOne_inner hv hv2 x x]
  apply integral_congr_ae
  filter_upwards with a
  ring

/-- The quadratic form of the integrated feature operator is nonnegative. -/
theorem realHilbertIntegratedSelfRankOne_inner_self_nonneg
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ)
    (x : H) :
    0 ≤ inner ℝ (realHilbertIntegratedSelfRankOne μ v x) x := by
  rw [realHilbertIntegratedSelfRankOne_inner_self hv hv2 x]
  exact integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun a => sq_nonneg (inner ℝ (v a) x))

/-- A square-integrable real-Hilbert feature family produces a positive
operator in Mathlib's Hilbert-space operator order. -/
theorem realHilbertIntegratedSelfRankOne_isPositive
    {μ : Measure α} {v : α → H}
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ) :
    ((realHilbertIntegratedSelfRankOne μ v : H →L[ℝ] H) : H →ₗ[ℝ] H).IsPositive := by
  rw [LinearMap.isPositive_iff]
  exact ⟨realHilbertIntegratedSelfRankOne_isSymmetric hv hv2,
    realHilbertIntegratedSelfRankOne_inner_self_nonneg hv hv2⟩

/-- Audit-visible package for the basis-free positive frame operator generated
by a square-integrable real-Hilbert feature family. -/
structure RealHilbertIntegratedSelfRankOnePositivePackage
    (μ : Measure α) (v : α → H) : Prop where
  aestronglyMeasurable : AEStronglyMeasurable v μ
  squareNormIntegrable : Integrable (fun a => ‖v a‖ ^ 2) μ
  symmetric :
    ((realHilbertIntegratedSelfRankOne μ v : H →L[ℝ] H) : H →ₗ[ℝ] H).IsSymmetric
  positive :
    ((realHilbertIntegratedSelfRankOne μ v : H →L[ℝ] H) : H →ₗ[ℝ] H).IsPositive
  quadraticForm :
    ∀ x : H,
      inner ℝ (realHilbertIntegratedSelfRankOne μ v x) x =
        ∫ a, (inner ℝ (v a) x) ^ 2 ∂μ

/-- The natural measurability and square-integrability hypotheses canonically
produce the complete positive integrated-feature receipt. -/
theorem realHilbertIntegratedSelfRankOnePositivePackage
    (μ : Measure α) (v : α → H)
    (hv : AEStronglyMeasurable v μ)
    (hv2 : Integrable (fun a => ‖v a‖ ^ 2) μ) :
    RealHilbertIntegratedSelfRankOnePositivePackage μ v :=
  { aestronglyMeasurable := hv
    squareNormIntegrable := hv2
    symmetric := realHilbertIntegratedSelfRankOne_isSymmetric hv hv2
    positive := realHilbertIntegratedSelfRankOne_isPositive hv hv2
    quadraticForm := realHilbertIntegratedSelfRankOne_inner_self hv hv2 }

end

end MathlibAnalytic
end MGAP4D
