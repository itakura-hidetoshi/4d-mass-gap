import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Extend a linear isometry canonically from a normed space to Mathlib's
uniform completion, using the completion embedding and the pinned
`LinearMap.extendOfNorm` API.

This is the pre-`LinearIsometry.fromCompletion` realization of the same
universal construction: the extension is first obtained as a continuous
linear map, and norm preservation is propagated from the canonical dense copy
of the source. -/
noncomputable def denseLinearIsometryCompletion
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F) :
    UniformSpace.Completion E →ₗᵢ[𝕜] F := by
  let e : E →ₗ[𝕜] UniformSpace.Completion E :=
    (UniformSpace.Completion.toComplₗᵢ 𝕜 E).toLinearMap
  have h_dense : DenseRange e := by
    simpa [e] using (UniformSpace.Completion.denseRange_coe (α := E))
  have h_bound : ∃ C : ℝ, ∀ x : E, ‖f.toLinearMap x‖ ≤ C * ‖e x‖ := by
    refine ⟨1, ?_⟩
    intro x
    simp [e]
  exact
    { __ := f.toLinearMap.extendOfNorm e
      norm_map' := by
        refine h_dense.induction ?_ (isClosed_eq (by fun_prop) continuous_norm)
        rintro _ ⟨x, rfl⟩
        rw [LinearMap.extendOfNorm_eq h_dense h_bound x]
        simp [e] }

/-- On the canonical dense copy of the source, the completion extension is
exactly the original linear isometry. -/
@[simp] theorem denseLinearIsometryCompletion_apply_coe
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F)
    (x : E) :
    denseLinearIsometryCompletion f
        (x : UniformSpace.Completion E) = f x := by
  let e : E →ₗ[𝕜] UniformSpace.Completion E :=
    (UniformSpace.Completion.toComplₗᵢ 𝕜 E).toLinearMap
  have h_dense : DenseRange e := by
    simpa [e] using (UniformSpace.Completion.denseRange_coe (α := E))
  have h_bound : ∃ C : ℝ, ∀ y : E, ‖f.toLinearMap y‖ ≤ C * ‖e y‖ := by
    refine ⟨1, ?_⟩
    intro y
    simp [e]
  change f.toLinearMap.extendOfNorm e (e x) = f x
  exact LinearMap.extendOfNorm_eq h_dense h_bound x

/-- A linear isometry with dense range into a complete normed space identifies
Mathlib's canonical uniform completion of its source with the target.

The construction uses only APIs present in the repository's pinned Mathlib:
extend along `UniformSpace.Completion.toComplₗᵢ` by
`LinearMap.extendOfNorm`, then use the original dense range and closedness of
the completed isometry range to obtain surjectivity, finally packaging it with
`LinearIsometryEquiv.ofSurjective`. -/
noncomputable def denseLinearIsometryCompletionEquiv
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F)
    (h_dense : DenseRange f) :
    UniformSpace.Completion E ≃ₗᵢ[𝕜] F :=
  LinearIsometryEquiv.ofSurjective (denseLinearIsometryCompletion f) <| by
    have h_sub :
        Set.range f ⊆ Set.range ⇑(denseLinearIsometryCompletion f) := by
      rintro _ ⟨x, rfl⟩
      exact ⟨(x : UniformSpace.Completion E), by simp⟩
    rw [← Set.range_eq_univ,
      ← (denseLinearIsometryCompletion f).isometry.isClosedEmbedding.isClosed_range.closure_eq,
      (h_dense.mono h_sub).closure_eq]

/-- On the canonical dense copy of the source, the completion equivalence is
exactly the original linear isometry. -/
@[simp] theorem denseLinearIsometryCompletionEquiv_apply_coe
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F)
    (h_dense : DenseRange f)
    (x : E) :
    denseLinearIsometryCompletionEquiv f h_dense
        (x : UniformSpace.Completion E) = f x := by
  change denseLinearIsometryCompletion f
      (x : UniformSpace.Completion E) = f x
  exact denseLinearIsometryCompletion_apply_coe f x

end

end MathlibAnalytic
end MGAP4D
