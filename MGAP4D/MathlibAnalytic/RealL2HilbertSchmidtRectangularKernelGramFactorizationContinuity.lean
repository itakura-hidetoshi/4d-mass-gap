import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelGramFactorization
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorContinuity
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Gram factorization is continuous in the product-`L²` kernel.

The proof deliberately factors the map into the already-established continuous
Hilbert--Schmidt analysis construction, the Hilbert adjoint (an isometric
conjugate-linear equivalence), and bounded bilinear composition.  Thus no
pointwise kernel representative is introduced. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_continuous
    [SFinite μ] [SFinite ν] :
    Continuous
      (fun K : Lp ℝ 2 (μ.prod ν) =>
        realL2HilbertSchmidtRectangularKernelFactorizedOperator K) := by
  let A := fun K : Lp ℝ 2 (μ.prod ν) =>
    realL2HilbertSchmidtRectangularKernelOperator K
  have hA : Continuous A := by
    simpa [A] using
      (realL2HilbertSchmidtRectangularKernelOperator_continuous
        (μ := μ) (ν := ν))
  have hAdj : Continuous (fun K : Lp ℝ 2 (μ.prod ν) => (A K)†) := by
    exact ContinuousLinearMap.adjoint.continuous.comp hA
  simpa [A, realL2HilbertSchmidtRectangularKernelFactorizedOperator] using
    hAdj.clm_comp hA

/-- Any convergent family of rectangular Hilbert--Schmidt kernels has
convergent canonical Gram factors `A_K† A_K` in operator norm. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_tendsto
    [SFinite μ] [SFinite ν]
    {ι : Type*} {l : Filter ι}
    {K : ι → Lp ℝ 2 (μ.prod ν)}
    {K∞ : Lp ℝ 2 (μ.prod ν)}
    (hK : Tendsto K l (𝓝 K∞)) :
    Tendsto
      (fun i => realL2HilbertSchmidtRectangularKernelFactorizedOperator (K i))
      l
      (𝓝 (realL2HilbertSchmidtRectangularKernelFactorizedOperator K∞)) := by
  exact
    ((realL2HilbertSchmidtRectangularKernelFactorizedOperator_continuous
      (μ := μ) (ν := ν)).tendsto K∞).comp hK

end

end MathlibAnalytic
end MGAP4D
