import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperator
import Mathlib.Topology.MetricSpace.Lipschitz

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- The Hilbert--Schmidt pairing is linear in its product-`L²` kernel.
This is the kernel-side identity needed to compare two rectangular operators
without choosing pointwise representatives. -/
theorem realL2HilbertSchmidtKernelPairing_sub_kernel
    [SFinite μ] [SFinite ν]
    (K₁ K₂ : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) (g : Lp ℝ 2 ν) :
    realL2HilbertSchmidtKernelPairing (K₁ - K₂) f g =
      realL2HilbertSchmidtKernelPairing K₁ f g -
        realL2HilbertSchmidtKernelPairing K₂ f g := by
  simp [realL2HilbertSchmidtKernelPairing, inner_sub_left]

/-- Passing from a product-`L²` kernel to its rectangular Fréchet--Riesz
operator preserves subtraction exactly. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_sub
    [SFinite μ] [SFinite ν]
    (K₁ K₂ : Lp ℝ 2 (μ.prod ν)) :
    realL2HilbertSchmidtRectangularKernelOperator (K₁ - K₂) =
      realL2HilbertSchmidtRectangularKernelOperator K₁ -
        realL2HilbertSchmidtRectangularKernelOperator K₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  simp [realL2HilbertSchmidtRectangularKernelOperator_inner,
    realL2HilbertSchmidtKernelPairing_sub_kernel, inner_sub_left]

/-- Sharp difference estimate: the rectangular operator construction is a
contraction from product-kernel `L²` norm to operator norm. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_sub_norm_le
    [SFinite μ] [SFinite ν]
    (K₁ K₂ : Lp ℝ 2 (μ.prod ν)) :
    ‖realL2HilbertSchmidtRectangularKernelOperator K₁ -
        realL2HilbertSchmidtRectangularKernelOperator K₂‖ ≤
      ‖K₁ - K₂‖ := by
  rw [← realL2HilbertSchmidtRectangularKernelOperator_sub]
  exact realL2HilbertSchmidtRectangularKernelOperator_norm_le (K₁ - K₂)

/-- The product-`L²` kernel-to-operator map is `1`-Lipschitz.  Consequently any
`L²` convergence of finite Wilson/Fock kernels automatically yields operator-
norm convergence of their rectangular analysis operators. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_lipschitz
    [SFinite μ] [SFinite ν] :
    LipschitzWith 1
      (fun K : Lp ℝ 2 (μ.prod ν) =>
        realL2HilbertSchmidtRectangularKernelOperator K) := by
  apply LipschitzWith.mk_one
  intro K₁ K₂
  simpa [dist_eq_norm] using
    realL2HilbertSchmidtRectangularKernelOperator_sub_norm_le K₁ K₂

/-- In particular, the rectangular Hilbert--Schmidt operator depends
continuously on its product-`L²` kernel. -/
theorem realL2HilbertSchmidtRectangularKernelOperator_continuous
    [SFinite μ] [SFinite ν] :
    Continuous
      (fun K : Lp ℝ 2 (μ.prod ν) =>
        realL2HilbertSchmidtRectangularKernelOperator K) :=
  realL2HilbertSchmidtRectangularKernelOperator_lipschitz.continuous

end

end MathlibAnalytic
end MGAP4D