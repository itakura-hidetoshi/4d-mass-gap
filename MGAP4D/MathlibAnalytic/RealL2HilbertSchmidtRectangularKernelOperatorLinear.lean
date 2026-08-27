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
  calc
    inner ℝ (realL2HilbertSchmidtRectangularKernelOperator (K + L) f) g =
        realL2HilbertSchmidtKernelPairing (K + L) f g :=
      realL2HilbertSchmidtRectangularKernelOperator_inner (K + L) f g
    _ = realL2HilbertSchmidtKernelPairing K f g +
        realL2HilbertSchmidtKernelPairing L f g := by
      simp [realL2HilbertSchmidtKernelPairing, inner_add_left]
    _ = inner ℝ (realL2HilbertSchmidtRectangularKernelOperator K f) g +
        inner ℝ (realL2HilbertSchmidtRectangularKernelOperator L f) g := by
      rw [realL2HilbertSchmidtRectangularKernelOperator_inner,
        realL2HilbertSchmidtRectangularKernelOperator_inner]
    _ = inner ℝ
        ((realL2HilbertSchmidtRectangularKernelOperator K +
          realL2HilbertSchmidtRectangularKernelOperator L) f) g := by
      simp [inner_add_left]

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
  calc
    inner ℝ (realL2HilbertSchmidtRectangularKernelOperator (c • K) f) g =
        realL2HilbertSchmidtKernelPairing (c • K) f g :=
      realL2HilbertSchmidtRectangularKernelOperator_inner (c • K) f g
    _ = c * realL2HilbertSchmidtKernelPairing K f g := by
      simp [realL2HilbertSchmidtKernelPairing, real_inner_smul_left]
    _ = c * inner ℝ (realL2HilbertSchmidtRectangularKernelOperator K f) g := by
      rw [realL2HilbertSchmidtRectangularKernelOperator_inner]
    _ = inner ℝ
        ((c • realL2HilbertSchmidtRectangularKernelOperator K) f) g := by
      simp [real_inner_smul_left]

/-- The canonical real-linear map sending a product-`L²` Hilbert--Schmidt
kernel to its bounded rectangular Fréchet--Riesz operator. -/
noncomputable def realL2HilbertSchmidtRectangularKernelToOperatorLinearMap
    [SFinite μ] [SFinite ν] :
    Lp ℝ 2 (μ.prod ν) →ₗ[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) where
  toFun := realL2HilbertSchmidtRectangularKernelOperator
  map_add' := realL2HilbertSchmidtRectangularKernelOperator_add
  map_smul' := realL2HilbertSchmidtRectangularKernelOperator_smul

@[simp] theorem realL2HilbertSchmidtRectangularKernelToOperatorLinearMap_apply
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelToOperatorLinearMap K =
      realL2HilbertSchmidtRectangularKernelOperator K :=
  rfl

/-- The kernel-to-operator linear map has pointwise norm bound one. -/
theorem realL2HilbertSchmidtRectangularKernelToOperatorLinearMap_apply_norm_le
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ‖realL2HilbertSchmidtRectangularKernelToOperatorLinearMap K‖ ≤ ‖K‖ := by
  exact realL2HilbertSchmidtRectangularKernelOperator_norm_le K

/-- The Hilbert--Schmidt kernel construction is canonically a bounded linear map
from product `L²` into the Banach space of bounded rectangular operators. -/
noncomputable def realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap
    [SFinite μ] [SFinite ν] :
    Lp ℝ 2 (μ.prod ν) →L[ℝ]
      (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν) :=
  LinearMap.mkContinuous
    (𝕜 := ℝ)
    (𝕜₂ := ℝ)
    (E := Lp ℝ 2 (μ.prod ν))
    (F := Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν)
    (σ := RingHom.id ℝ)
    realL2HilbertSchmidtRectangularKernelToOperatorLinearMap
    1
    (by
      intro K
      simpa using
        realL2HilbertSchmidtRectangularKernelToOperatorLinearMap_apply_norm_le K)

@[simp] theorem realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap_apply
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap K =
      realL2HilbertSchmidtRectangularKernelOperator K :=
  rfl

/-- The operator norm of the kernel-to-operator bounded linear map is at most
one. -/
theorem realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap_norm_le_one
    [SFinite μ] [SFinite ν] :
    ‖(realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap
        (μ := μ) (ν := ν))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound
    realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap
    zero_le_one
  intro K
  simpa using
    realL2HilbertSchmidtRectangularKernelToOperatorLinearMap_apply_norm_le K

/-- Audit-visible receipt for the linear and bounded dependence of the
rectangular Hilbert--Schmidt operator on its kernel. -/
structure RealL2HilbertSchmidtRectangularKernelToOperatorPackage
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
    ‖(realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap
        (μ := μ) (ν := ν))‖ ≤ 1

/-- Construct the bounded kernel-linearity package. -/
theorem realL2HilbertSchmidtRectangularKernelToOperatorPackage
    [SFinite μ] [SFinite ν] :
    RealL2HilbertSchmidtRectangularKernelToOperatorPackage
      (μ := μ) (ν := ν) :=
  { additivity := realL2HilbertSchmidtRectangularKernelOperator_add
    homogeneity := realL2HilbertSchmidtRectangularKernelOperator_smul
    normBound :=
      realL2HilbertSchmidtRectangularKernelToOperatorContinuousLinearMap_norm_le_one }

end

end MathlibAnalytic
end MGAP4D
