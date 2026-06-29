import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

noncomputable section

/-- A uniformly operator-norm-bounded family of continuous linear maps is
uniformly equicontinuous. -/
theorem uniformlyBoundedContinuousLinearMap_uniformEquicontinuous
    {ι E F : Type*}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ E]
    [NormedSpace ℝ F]
    (A : ι → E →L[ℝ] F)
    (K : NNReal)
    (hA : ∀ i, ‖A i‖₊ ≤ K) :
    UniformEquicontinuous (fun i x => A i x) := by
  apply LipschitzWith.uniformEquicontinuous
    (fun i x => A i x) K
  intro i
  exact (A i).lipschitz.weaken (hA i)

/-- Pointwise convergence of a uniformly bounded family of continuous linear
maps extends from the range of any dense map to the whole normed space.

The target map only needs to be continuous; no completeness assumption on the
source or target space is required. -/
theorem uniformlyBoundedContinuousLinearMap_tendsto_of_denseRange
    {ι Q E F : Type*}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ E]
    [NormedSpace ℝ F]
    {l : Filter ι}
    (A : ι → E →L[ℝ] F)
    (B : E →L[ℝ] F)
    (K : NNReal)
    (hA : ∀ i, ‖A i‖₊ ≤ K)
    (q : Q → E)
    (hq : DenseRange q)
    (hRange : ∀ z : Q,
      Tendsto (fun i => A i (q z)) l (𝓝 (B (q z)))) :
    ∀ x : E, Tendsto (fun i => A i x) l (𝓝 (B x)) := by
  let S : Set E :=
    {x | Tendsto (fun i => A i x) l (𝓝 (B x))}
  have hEquicontinuous :
      Equicontinuous (fun i x => A i x) :=
    (uniformlyBoundedContinuousLinearMap_uniformEquicontinuous
      A K hA).equicontinuous
  have hClosed : IsClosed S := by
    exact hEquicontinuous.isClosed_setOf_tendsto B.continuous
  have hRangeSubset : Set.range q ⊆ S := by
    rintro _ ⟨z, rfl⟩
    exact hRange z
  intro x
  exact (closure_minimal hRangeSubset hClosed) (hq x)

/-- Set-valued version: convergence on a dense subset extends to every point. -/
theorem uniformlyBoundedContinuousLinearMap_tendsto_of_dense
    {ι E F : Type*}
    [NormedAddCommGroup E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ E]
    [NormedSpace ℝ F]
    {l : Filter ι}
    (A : ι → E →L[ℝ] F)
    (B : E →L[ℝ] F)
    (K : NNReal)
    (hA : ∀ i, ‖A i‖₊ ≤ K)
    (s : Set E)
    (hs : Dense s)
    (hDense : ∀ x ∈ s,
      Tendsto (fun i => A i x) l (𝓝 (B x))) :
    ∀ x : E, Tendsto (fun i => A i x) l (𝓝 (B x)) := by
  let q : s → E := fun x => x.1
  have hq : DenseRange q := by
    simpa only [q, Subtype.range_val] using hs
  apply uniformlyBoundedContinuousLinearMap_tendsto_of_denseRange
    A B K hA q hq
  intro x
  exact hDense x.1 x.2

end

end MathlibAnalytic
end MGAP4D
