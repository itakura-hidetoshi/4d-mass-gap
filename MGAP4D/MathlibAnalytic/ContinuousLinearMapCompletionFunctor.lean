import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

noncomputable section

/-- Mathlib's native completion functor does not increase the operator norm of
a bounded linear map between normed spaces.  The proof is the dense-copy
argument: the usual operator bound holds on the canonical copy of the source,
and both sides are continuous on the completion. -/
theorem continuousLinearMap_completion_opNorm_le
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (f : E →L[𝕜] F) :
    ‖f.completion‖ ≤ ‖f‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact norm_nonneg f
  · intro x
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro a
      simpa using f.le_opNorm a

/-- Completion is functorial for composition of bounded linear maps. -/
theorem continuousLinearMap_completion_comp
    {𝕜 E F G : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    [NormedAddCommGroup G]
    [NormedSpace 𝕜 G]
    (f : F →L[𝕜] G)
    (g : E →L[𝕜] F) :
    (f ∘L g).completion = f.completion ∘L g.completion := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro a
    simp

/-- Completion preserves the identity bounded linear map. -/
@[simp] theorem continuousLinearMap_completion_id
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] :
    (ContinuousLinearMap.id 𝕜 E).completion =
      ContinuousLinearMap.id 𝕜 (UniformSpace.Completion E) := by
  apply ContinuousLinearMap.ext
  intro x
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro a
    simp

end

end MathlibAnalytic
end MGAP4D
