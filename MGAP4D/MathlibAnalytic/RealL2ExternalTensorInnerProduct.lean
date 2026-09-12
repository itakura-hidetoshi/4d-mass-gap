import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtSeparableKernelOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- The rectangular Hilbert--Schmidt operator associated with a separable real
`L²` kernel has the exact rank-one operator norm

`‖T_(u ⊠ v)‖ = ‖u‖ ‖v‖`.

The upper bound is the existing Hilbert--Schmidt estimate together with the
exact external-tensor cross norm.  For the reverse inequality we test the
rank-one formula on the normalized vector `‖u‖⁻¹ • u`. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_externalTensor_norm
    [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) :
    ‖realL2HilbertSchmidtRectangularKernelOperator
        (realL2ExternalTensor u v)‖ =
      ‖u‖ * ‖v‖ := by
  apply le_antisymm
  · calc
      ‖realL2HilbertSchmidtRectangularKernelOperator
          (realL2ExternalTensor u v)‖ ≤
          ‖realL2ExternalTensor u v‖ :=
        realL2HilbertSchmidtRectangularKernelOperator_norm_le
          (realL2ExternalTensor u v)
      _ = ‖u‖ * ‖v‖ := realL2ExternalTensor_norm u v
  · by_cases hu : u = 0
    · simp [hu]
    · let e : Lp ℝ 2 μ := ‖u‖⁻¹ • u
      have huNorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
      have he_norm : ‖e‖ = 1 := by
        dsimp [e]
        rw [norm_smul, Real.norm_eq_abs, abs_inv,
          abs_of_nonneg (norm_nonneg u)]
        exact inv_mul_cancel₀ huNorm
      have hinner : inner ℝ u e = ‖u‖ := by
        dsimp [e]
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      calc
        ‖u‖ * ‖v‖ = ‖(inner ℝ u e) • v‖ := by
          rw [hinner, norm_smul,
            Real.norm_of_nonneg (norm_nonneg u)]
        _ = ‖realL2HilbertSchmidtRectangularKernelOperator
              (realL2ExternalTensor u v) e‖ := by
          rw [realL2HilbertSchmidtRectangularKernelOperator_externalTensor_apply]
        _ ≤ ‖realL2HilbertSchmidtRectangularKernelOperator
              (realL2ExternalTensor u v)‖ * ‖e‖ :=
          (realL2HilbertSchmidtRectangularKernelOperator
            (realL2ExternalTensor u v)).le_opNorm e
        _ = ‖realL2HilbertSchmidtRectangularKernelOperator
              (realL2ExternalTensor u v)‖ := by
          rw [he_norm, mul_one]

/-- A separable Hilbert--Schmidt operator vanishes exactly when at least one of
its two rank-one factors vanishes. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_externalTensor_eq_zero_iff
    [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) :
    realL2HilbertSchmidtRectangularKernelOperator
        (realL2ExternalTensor u v) = 0 ↔
      u = 0 ∨ v = 0 := by
  rw [← norm_eq_zero]
  rw [realL2HilbertSchmidtRectangularKernelOperator_externalTensor_norm]
  rw [mul_eq_zero]
  simp

/-- Audit-visible receipt for the exact separable-kernel rank-one calculus.
The inner-product and pointwise rank-one formulas are inherited from
`RealL2HilbertSchmidtSeparableKernelOperator`; this unit adds the sharp operator
norm and nondegeneracy statement. -/
structure RealL2SeparableKernelExactOperatorPackage
    [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) : Prop where
  operatorFormula :
    ∀ f : Lp ℝ 2 μ,
      realL2HilbertSchmidtRectangularKernelOperator
          (realL2ExternalTensor u v) f =
        (inner ℝ u f) • v
  operatorNorm :
    ‖realL2HilbertSchmidtRectangularKernelOperator
        (realL2ExternalTensor u v)‖ =
      ‖u‖ * ‖v‖
  operatorEqZero :
    realL2HilbertSchmidtRectangularKernelOperator
        (realL2ExternalTensor u v) = 0 ↔
      u = 0 ∨ v = 0

/-- Construct the exact separable-kernel rank-one operator package. -/
theorem realL2SeparableKernelExactOperatorPackage
    [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) :
    RealL2SeparableKernelExactOperatorPackage u v :=
  { operatorFormula :=
      realL2HilbertSchmidtRectangularKernelOperator_externalTensor_apply u v
    operatorNorm :=
      realL2HilbertSchmidtRectangularKernelOperator_externalTensor_norm u v
    operatorEqZero :=
      realL2HilbertSchmidtRectangularKernelOperator_externalTensor_eq_zero_iff u v }

end

end MathlibAnalytic
end MGAP4D
