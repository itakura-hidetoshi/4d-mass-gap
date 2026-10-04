import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorContinuity
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Continuity of the square real Hilbert--Schmidt kernel operator

The square Fréchet--Riesz kernel-operator construction is linear in the
product-L² kernel and is a contraction from kernel L² norm to operator norm.

This is the square analogue of the existing rectangular continuity API.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- Passing from a square product-L² kernel to its Fréchet--Riesz operator
preserves subtraction exactly. -/
theorem realL2HilbertSchmidtKernelOperator_sub
    [SFinite μ]
    (K₁ K₂ : Lp ℝ 2 (μ.prod μ)) :
    realL2HilbertSchmidtKernelOperator (K₁ - K₂) =
      realL2HilbertSchmidtKernelOperator K₁ -
        realL2HilbertSchmidtKernelOperator K₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_right ℝ
  intro g
  change inner ℝ
      (realL2HilbertSchmidtKernelOperator (K₁ - K₂) f) g =
    inner ℝ
      (realL2HilbertSchmidtKernelOperator K₁ f -
        realL2HilbertSchmidtKernelOperator K₂ f) g
  rw [realL2HilbertSchmidtKernelOperator_inner,
    inner_sub_left,
    realL2HilbertSchmidtKernelOperator_inner,
    realL2HilbertSchmidtKernelOperator_inner]
  exact realL2HilbertSchmidtKernelPairing_sub_kernel K₁ K₂ f g

/-- Sharp square-kernel difference estimate. -/
theorem realL2HilbertSchmidtKernelOperator_sub_norm_le
    [SFinite μ]
    (K₁ K₂ : Lp ℝ 2 (μ.prod μ)) :
    ‖realL2HilbertSchmidtKernelOperator K₁ -
        realL2HilbertSchmidtKernelOperator K₂‖ ≤
      ‖K₁ - K₂‖ := by
  rw [← realL2HilbertSchmidtKernelOperator_sub]
  exact realL2HilbertSchmidtKernelOperator_norm_le (K₁ - K₂)

/-- The square Hilbert--Schmidt kernel-to-operator map is 1-Lipschitz. -/
theorem realL2HilbertSchmidtKernelOperator_lipschitz
    [SFinite μ] :
    LipschitzWith 1
      (fun K : Lp ℝ 2 (μ.prod μ) =>
        realL2HilbertSchmidtKernelOperator K) := by
  apply LipschitzWith.mk_one
  intro K₁ K₂
  simpa [dist_eq_norm] using
    realL2HilbertSchmidtKernelOperator_sub_norm_le K₁ K₂

end

end MathlibAnalytic
end MGAP4D
