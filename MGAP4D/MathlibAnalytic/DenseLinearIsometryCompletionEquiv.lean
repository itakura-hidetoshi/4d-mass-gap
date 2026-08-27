import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A linear isometry with dense range into a complete normed space identifies
Mathlib's canonical uniform completion of its source with the target.

The construction is entirely native: extend the isometry by
`LinearIsometry.fromCompletion`, prove the extended range is both closed and
dense using the original dense range, then package surjectivity with
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
  LinearIsometryEquiv.ofSurjective f.fromCompletion <| by
    have h_sub : Set.range f ⊆ Set.range ⇑f.fromCompletion := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x, f.fromCompletion_apply_coe x⟩
    rw [← Set.range_eq_univ,
      ← f.fromCompletion.isometry.isClosedEmbedding.isClosed_range.closure_eq,
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
  change f.fromCompletion (x : UniformSpace.Completion E) = f x
  exact f.fromCompletion_apply_coe x

end

end MathlibAnalytic
end MGAP4D
