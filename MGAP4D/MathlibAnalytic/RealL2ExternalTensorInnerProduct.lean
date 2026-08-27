import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
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

/-- The real `L²` external tensor preserves the Hilbert tensor-product inner
product exactly.  This is the bilinear strengthening of the cross-norm theorem
in `RealL2ExternalTensor` and is the basic rank-one identity needed to read a
two-boundary `L²` kernel as a Hilbert--Schmidt operator. -/
theorem realL2ExternalTensor_inner
    [SFinite μ] [SFinite ν]
    (f₁ f₂ : Lp ℝ 2 μ)
    (g₁ g₂ : Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensor f₁ g₁)
        (realL2ExternalTensor f₂ g₂) =
      inner ℝ f₁ f₂ * inner ℝ g₁ g₂ := by
  rw [MeasureTheory.L2.inner_def]
  have hfInt :
      Integrable (fun a => inner ℝ (f₁ a) (f₂ a)) μ :=
    MeasureTheory.L2.integrable_inner f₁ f₂
  have hgInt :
      Integrable (fun b => inner ℝ (g₁ b) (g₂ b)) ν :=
    MeasureTheory.L2.integrable_inner g₁ g₂
  calc
    (∫ z, inner ℝ (realL2ExternalTensor f₁ g₁ z)
        (realL2ExternalTensor f₂ g₂ z) ∂(μ.prod ν)) =
        ∫ z : α × β,
          inner ℝ (f₁ z.1) (f₂ z.1) *
            inner ℝ (g₁ z.2) (g₂ z.2) ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards [realL2ExternalTensor_coeFn f₁ g₁,
        realL2ExternalTensor_coeFn f₂ g₂] with z h₁ h₂
      rw [h₁, h₂]
      simp only [realL2ExternalTensorFunction]
      change
        (f₁ z.1 * g₁ z.2) * (f₂ z.1 * g₂ z.2) =
          (f₁ z.1 * f₂ z.1) * (g₁ z.2 * g₂ z.2)
      ring
    _ = (∫ a, inner ℝ (f₁ a) (f₂ a) ∂μ) *
        ∫ b, inner ℝ (g₁ b) (g₂ b) ∂ν := by
      exact integral_prod_mul
        (fun a => inner ℝ (f₁ a) (f₂ a))
        (fun b => inner ℝ (g₁ b) (g₂ b))
    _ = inner ℝ f₁ f₂ * inner ℝ g₁ g₂ := by
      rw [← MeasureTheory.L2.inner_def, ← MeasureTheory.L2.inner_def]

/-- Pairing a rank-one external tensor kernel against another pure external
tensor factors into the product of the two one-slice matrix coefficients. -/
theorem realL2HilbertSchmidtKernelPairing_externalTensor
    [SFinite μ] [SFinite ν]
    (u f : Lp ℝ 2 μ)
    (v g : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing
        (realL2ExternalTensor u v) f g =
      inner ℝ u f * inner ℝ v g := by
  exact realL2ExternalTensor_inner u f v g

/-- On a square `L²` carrier, the Hilbert--Schmidt operator of the rank-one
kernel `u ⊠ v` is the usual rank-one map

`f ↦ ⟪u,f⟫ v`.

This identifies the existing kernel/Riesz construction with ordinary Hilbert
space rank-one calculus without choosing pointwise representatives. -/
theorem realL2HilbertSchmidtKernelOperator_externalTensor_apply
    [SFinite μ]
    (u v f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtKernelOperator (realL2ExternalTensor u v) f =
      (inner ℝ u f) • v := by
  refine ext_inner_right ℝ ?_
  intro g
  calc
    inner ℝ
        (realL2HilbertSchmidtKernelOperator (realL2ExternalTensor u v) f) g =
      realL2HilbertSchmidtKernelPairing
        (realL2ExternalTensor u v) f g :=
      realL2HilbertSchmidtKernelOperator_inner
        (realL2ExternalTensor u v) f g
    _ = inner ℝ u f * inner ℝ v g :=
      realL2HilbertSchmidtKernelPairing_externalTensor u f v g
    _ = inner ℝ ((inner ℝ u f) • v) g := by
      rw [inner_smul_left]
      simp

/-- Exact operator norm of a rank-one real Hilbert--Schmidt kernel operator. -/
theorem realL2HilbertSchmidtKernelOperator_externalTensor_norm
    [SFinite μ]
    (u v : Lp ℝ 2 μ) :
    ‖realL2HilbertSchmidtKernelOperator (realL2ExternalTensor u v)‖ =
      ‖u‖ * ‖v‖ := by
  apply le_antisymm
  · calc
      ‖realL2HilbertSchmidtKernelOperator (realL2ExternalTensor u v)‖ ≤
          ‖realL2ExternalTensor u v‖ :=
        realL2HilbertSchmidtKernelOperator_norm_le
          (realL2ExternalTensor u v)
      _ = ‖u‖ * ‖v‖ := realL2ExternalTensor_norm u v
  · by_cases hu : u = 0
    · simp [hu]
    · let e : Lp ℝ 2 μ := ‖u‖⁻¹ • u
      have he_norm : ‖e‖ = 1 := by
        have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
        simp [e, norm_smul, hu_norm_pos.ne']
      have hinner : inner ℝ u e = ‖u‖ := by
        dsimp [e]
        rw [inner_smul_right]
        rw [real_inner_self_eq_norm_sq]
        have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
        field_simp
      calc
        ‖u‖ * ‖v‖ = ‖(inner ℝ u e) • v‖ := by
          rw [hinner, norm_smul, Real.norm_of_nonneg (norm_nonneg u)]
        _ = ‖realL2HilbertSchmidtKernelOperator
              (realL2ExternalTensor u v) e‖ := by
          rw [realL2HilbertSchmidtKernelOperator_externalTensor_apply]
        _ ≤ ‖realL2HilbertSchmidtKernelOperator
              (realL2ExternalTensor u v)‖ * ‖e‖ :=
          (realL2HilbertSchmidtKernelOperator
            (realL2ExternalTensor u v)).le_opNorm e
        _ = ‖realL2HilbertSchmidtKernelOperator
              (realL2ExternalTensor u v)‖ := by rw [he_norm, mul_one]

/-- Audit-visible receipt for the exact rank-one Hilbert--Schmidt calculus. -/
structure RealL2ExternalTensorInnerProductPackage
    [SFinite μ]
    (u v : Lp ℝ 2 μ) : Prop where
  tensorInner :
    ∀ f g : Lp ℝ 2 μ,
      inner ℝ (realL2ExternalTensor u v) (realL2ExternalTensor f g) =
        inner ℝ u f * inner ℝ v g
  operatorFormula :
    ∀ f : Lp ℝ 2 μ,
      realL2HilbertSchmidtKernelOperator (realL2ExternalTensor u v) f =
        (inner ℝ u f) • v
  operatorNorm :
    ‖realL2HilbertSchmidtKernelOperator (realL2ExternalTensor u v)‖ =
      ‖u‖ * ‖v‖

/-- Construct the exact rank-one Hilbert--Schmidt calculus package. -/
theorem realL2ExternalTensorInnerProductPackage
    [SFinite μ]
    (u v : Lp ℝ 2 μ) :
    RealL2ExternalTensorInnerProductPackage u v :=
  { tensorInner := fun f g => realL2ExternalTensor_inner u f v g
    operatorFormula :=
      realL2HilbertSchmidtKernelOperator_externalTensor_apply u v
    operatorNorm :=
      realL2HilbertSchmidtKernelOperator_externalTensor_norm u v }

end

end MathlibAnalytic
end MGAP4D
