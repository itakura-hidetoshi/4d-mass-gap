import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelGramFactorization
import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperatorContinuity
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory
open scoped InnerProductSpace InnerProduct Topology

noncomputable section

universe u v w

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
    {Klimit : Lp ℝ 2 (μ.prod ν)}
    (hK : Tendsto K l (𝓝 Klimit)) :
    Tendsto
      (fun i => realL2HilbertSchmidtRectangularKernelFactorizedOperator (K i))
      l
      (𝓝 (realL2HilbertSchmidtRectangularKernelFactorizedOperator Klimit)) := by
  exact
    ((realL2HilbertSchmidtRectangularKernelFactorizedOperator_continuous
      (μ := μ) (ν := ν)).tendsto Klimit).comp hK

/-- Operator-norm convergence on a real Hilbert space passes to every fixed
quadratic form `T ↦ ⟪T f, f⟫`.  This generic lemma keeps later model-specific
proofs free of expanded `L²` carrier types. -/
theorem continuousLinearMap_fixedQuadratic_tendsto
    {E : Type w}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} {l : Filter ι}
    {Gd : ι → (E →L[ℝ] E)} {G : E →L[ℝ] E}
    (hG : Tendsto Gd l (𝓝 G))
    (f : E) :
    Tendsto
      (fun i => inner ℝ (Gd i f) f)
      l
      (𝓝 (inner ℝ (G f) f)) := by
  have hEval : Continuous (fun T : E →L[ℝ] E => T f) := by
    exact continuous_id.clm_apply continuous_const
  have hApply : Tendsto (fun i => Gd i f) l (𝓝 (G f)) :=
    (hEval.tendsto G).comp hG
  exact hApply.inner tendsto_const_nhds

end

end MathlibAnalytic
end MGAP4D
