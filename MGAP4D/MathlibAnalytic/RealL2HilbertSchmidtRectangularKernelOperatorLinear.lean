import MGAP4D.MathlibAnalytic.RealL2ExternalTensorInnerProduct
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

/-- The Fréchet--Riesz rectangular Hilbert--Schmidt operator is additive in its
`L²` kernel. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_add
    [SFinite μ] [SFinite ν]
    (K L : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelOperator (K + L) =
      realL2HilbertSchmidtRectangularKernelOperator K +
        realL2HilbertSchmidtRectangularKernelOperator L := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp [realL2HilbertSchmidtRectangularKernelOperator_inner,
    realL2HilbertSchmidtKernelPairing, inner_add_left]

/-- The Fréchet--Riesz rectangular Hilbert--Schmidt operator is real-linear in
its `L²` kernel. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_smul
    [SFinite μ] [SFinite ν]
    (c : ℝ) (K : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelOperator (c • K) =
      c • realL2HilbertSchmidtRectangularKernelOperator K := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp [realL2HilbertSchmidtRectangularKernelOperator_inner,
    realL2HilbertSchmidtKernelPairing, real_inner_smul_left]

/-- The canonical real-linear map sending a product-`L²` Hilbert--Schmidt
kernel to its bounded rectangular Fréchet--Riesz operator. -/
noncomputable def realL2HilbertSchmidtRectangularKernelOperatorLinearMap
    [SFinite μ] [SFinite ν] :
    Lp ℝ 2 (μ.prod ν) →ₗ[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) where
  toFun := realL2HilbertSchmidtRectangularKernelOperator
  map_add' := realL2HilbertSchmidtRectangularKernelOperator_add
  map_smul' := realL2HilbertSchmidtRectangularKernelOperator_smul

@[simp] theorem realL2HilbertSchmidtRectangularKernelOperatorLinearMap_apply
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelOperatorLinearMap K =
      realL2HilbertSchmidtRectangularKernelOperator K :=
  rfl

/-- The kernel-to-operator linear map has pointwise norm bound one. -/
theorem realL2HilbertSchmidtRectangularKernelOperatorLinearMap_apply_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ‖realL2HilbertSchmidtRectangularKernelOperatorLinearMap K‖ ≤ ‖K‖ := by
  exact realL2HilbertSchmidtRectangularKernelOperator_norm_le K

/-- The Hilbert--Schmidt kernel construction is canonically a bounded linear map
from product `L²` into the Banach space of bounded rectangular operators. -/
noncomputable def realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap
    [SFinite μ] [SFinite ν] :
    Lp ℝ 2 (μ.prod ν) →L[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) :=
  LinearMap.mkContinuous
    (𝕜 := ℝ)
    (𝕜₂ := ℝ)
    (E := Lp ℝ 2 (μ.prod ν))
    (F := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (σ := RingHom.id ℝ)
    realL2HilbertSchmidtRectangularKernelOperatorLinearMap
    1
    (by
      intro K
      simpa using
        realL2HilbertSchmidtRectangularKernelOperatorLinearMap_apply_norm_le K)

@[simp] theorem realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap_apply
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap K =
      realL2HilbertSchmidtRectangularKernelOperator K :=
  rfl

/-- The operator norm of the kernel-to-operator bounded linear map is at most
one. -/
theorem realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap_norm_le_one
    [SFinite μ] [SFinite ν] :
    ‖(realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap
        (μ := μ) (ν := ν))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap
    zero_le_one
  intro K
  simpa using
    realL2HilbertSchmidtRectangularKernelOperatorLinearMap_apply_norm_le K

/-- Audit-visible receipt for the linear and bounded dependence of the
rectangular Hilbert--Schmidt operator on its kernel. -/
structure RealL2HilbertSchmidtRectangularKernelOperatorLinearPackage
    [SFinite μ] [SFinite ν] : Prop where
  additivity :
    ∀ K L : Lp ℝ 2 (μ.prod ν),
      realL2HilbertSchmidtRectangularKernelOperator (K + L) =
        realL2HilbertSchmidtRectangularKernelOperator K +
          realL2HilbertSchmidtRectangularKernelOperator L
  homogeneity :
    ∀ (c : ℝ) (K : Lp ℝ 2 (μ.prod ν)),
      realL2HilbertSchmidtRectangularKernelOperator (c • K) =
        c • realL2HilbertSchmidtRectangularKernelOperator K
  normBound :
    ‖(realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap
        (μ := μ) (ν := ν))‖ ≤ 1

/-- Construct the bounded kernel-linearity package. -/
theorem realL2HilbertSchmidtRectangularKernelOperatorLinearPackage
    [SFinite μ] [SFinite ν] :
    RealL2HilbertSchmidtRectangularKernelOperatorLinearPackage
      (μ := μ) (ν := ν) :=
  { additivity := realL2HilbertSchmidtRectangularKernelOperator_add
    homogeneity := realL2HilbertSchmidtRectangularKernelOperator_smul
    normBound :=
      realL2HilbertSchmidtRectangularKernelOperatorContinuousLinearMap_norm_le_one }

end

end MathlibAnalytic
end MGAP4D
