import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperator
import Mathlib.Analysis.InnerProductSpace.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- The real scalar inner product is ordinary multiplication. -/
theorem realScalar_inner_eq_mul (a b : ℝ) :
    inner ℝ a b = a * b := by
  have h11 : inner ℝ (1 : ℝ) (1 : ℝ) = 1 := by
    simpa using (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (1 : ℝ))
  calc
    inner ℝ a b = inner ℝ (a • (1 : ℝ)) (b • (1 : ℝ)) := by simp
    _ = a * inner ℝ (1 : ℝ) (b • (1 : ℝ)) := by
      rw [real_inner_smul_left]
    _ = a * (b * inner ℝ (1 : ℝ) (1 : ℝ)) := by
      rw [real_inner_smul_right]
    _ = a * b := by
      rw [h11]
      ring

/-- The real `L²` external tensor is a genuine Hilbert tensor on decomposable
vectors: its inner product factors into the product of the two factor inner
products. -/
theorem realL2ExternalTensor_inner
    [SFinite μ] [SFinite ν]
    (u f : Lp ℝ 2 μ) (v g : Lp ℝ 2 ν) :
    inner ℝ (realL2ExternalTensor u v) (realL2ExternalTensor f g) =
      inner ℝ u f * inner ℝ v g := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ z, inner ℝ
        (realL2ExternalTensor u v z)
        (realL2ExternalTensor f g z) ∂(μ.prod ν)) =
      ∫ z : α × β,
        inner ℝ (u z.1) (f z.1) * inner ℝ (v z.2) (g z.2)
        ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards
        [realL2ExternalTensor_coeFn u v,
          realL2ExternalTensor_coeFn f g] with z huv hfg
      rw [huv, hfg]
      simp only [realL2ExternalTensorFunction]
      rw [realScalar_inner_eq_mul,
        realScalar_inner_eq_mul, realScalar_inner_eq_mul]
      ring
    _ = (∫ a, inner ℝ (u a) (f a) ∂μ) *
        ∫ b, inner ℝ (v b) (g b) ∂ν := by
      exact integral_prod_mul
        (fun a => inner ℝ (u a) (f a))
        (fun b => inner ℝ (v b) (g b))
    _ = inner ℝ u f * inner ℝ v g := by
      rw [← MeasureTheory.L2.inner_def, ← MeasureTheory.L2.inner_def]

/-- Pairing a separable Hilbert--Schmidt kernel against a decomposable test
vector factors exactly into the two Hilbert inner products. -/
theorem realL2HilbertSchmidtKernelPairing_externalTensor
    [SFinite μ] [SFinite ν]
    (u f : Lp ℝ 2 μ) (v g : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing
        (realL2ExternalTensor u v) f g =
      inner ℝ u f * inner ℝ v g := by
  unfold realL2HilbertSchmidtKernelPairing
  exact realL2ExternalTensor_inner u f v g

/-- The rectangular Hilbert--Schmidt operator associated with a separable
kernel `u ⊠ v` is the rank-one map

`f ↦ ⟪u,f⟫ • v`.

This is the generic Mathlib-level rank-one formula used below for the
zero-coupling Wilson feature. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_externalTensor_apply
    [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtRectangularKernelOperator
        (realL2ExternalTensor u v) f =
      (inner ℝ u f) • v := by
  apply ext_inner_right ℝ
  intro g
  rw [realL2HilbertSchmidtRectangularKernelOperator_inner,
    realL2HilbertSchmidtKernelPairing_externalTensor,
    real_inner_smul_left]

/-- Every output of a separable-kernel Hilbert--Schmidt operator lies in the
one-dimensional span of its right factor. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_externalTensor_mem_span_singleton
    [SFinite μ] [SFinite ν]
    (u : Lp ℝ 2 μ) (v : Lp ℝ 2 ν) (f : Lp ℝ 2 μ) :
    realL2HilbertSchmidtRectangularKernelOperator
        (realL2ExternalTensor u v) f ∈
      Submodule.span ℝ ({v} : Set (Lp ℝ 2 ν)) := by
  rw [realL2HilbertSchmidtRectangularKernelOperator_externalTensor_apply]
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_singleton v))

end

end MathlibAnalytic
end MGAP4D
