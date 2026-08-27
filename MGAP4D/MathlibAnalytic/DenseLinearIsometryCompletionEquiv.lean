import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

private noncomputable def denseLinearIsometryRangeEquiv
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) :
    E ≃ₗ[𝕜] LinearMap.range f.toLinearMap :=
  LinearEquiv.ofInjective f.toLinearMap f.injective

private noncomputable def denseLinearIsometryCompletionEmbedding
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] :
    E →ₗ[𝕜] UniformSpace.Completion E :=
  (UniformSpace.Completion.toComplₗᵢ :
    E →ₗᵢ[𝕜] UniformSpace.Completion E).toLinearMap

private noncomputable def denseLinearIsometryRangeEmbedding
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F) :
    LinearMap.range f.toLinearMap →ₗ[𝕜] F :=
  (LinearMap.range f.toLinearMap).subtype

private theorem denseLinearIsometryCompletionEmbedding_denseRange
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] :
    DenseRange
      (denseLinearIsometryCompletionEmbedding (𝕜 := 𝕜) (E := E)) := by
  simpa [denseLinearIsometryCompletionEmbedding] using
    (UniformSpace.Completion.denseRange_coe (α := E))

private theorem denseLinearIsometryRangeEmbedding_denseRange
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F)
    (h_dense : DenseRange f) :
    DenseRange (denseLinearIsometryRangeEmbedding f) := by
  apply h_dense.mono
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨f x, ⟨x, rfl⟩⟩, rfl⟩

private theorem denseLinearIsometryRangeEquiv_norm
    {𝕜 E F : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E]
    [NormedSpace 𝕜 E]
    [NormedAddCommGroup F]
    [NormedSpace 𝕜 F]
    (f : E →ₗᵢ[𝕜] F)
    (x : E) :
    ‖denseLinearIsometryRangeEmbedding f (denseLinearIsometryRangeEquiv f x)‖ =
      ‖denseLinearIsometryCompletionEmbedding (𝕜 := 𝕜) (E := E) x‖ := by
  simpa [denseLinearIsometryRangeEmbedding,
    denseLinearIsometryRangeEquiv,
    denseLinearIsometryCompletionEmbedding] using f.norm_map x

/-- A linear isometry with dense range into a complete normed space identifies
Mathlib's canonical uniform completion of its source with the target.

The construction is entirely native to the repository's pinned Mathlib.  First
identify the source algebraically with the range of the isometry.  Then extend
that algebraic equivalence by `LinearEquiv.extendOfIsometry` along the two dense
maps

`E → UniformSpace.Completion E`

and

`LinearMap.range f → F`.

Thus no custom Cauchy-sequence completion and no hand-built inverse are used. -/
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
  (denseLinearIsometryRangeEquiv f).extendOfIsometry
    (denseLinearIsometryCompletionEmbedding (𝕜 := 𝕜) (E := E))
    (denseLinearIsometryRangeEmbedding f)
    (denseLinearIsometryCompletionEmbedding_denseRange (𝕜 := 𝕜) (E := E))
    (denseLinearIsometryRangeEmbedding_denseRange f h_dense)
    (denseLinearIsometryRangeEquiv_norm f)

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
  simpa [denseLinearIsometryCompletionEquiv,
    denseLinearIsometryCompletionEmbedding,
    denseLinearIsometryRangeEmbedding,
    denseLinearIsometryRangeEquiv] using
    (LinearEquiv.extendOfIsometry_eq
      (f := denseLinearIsometryRangeEquiv f)
      (e₁ := denseLinearIsometryCompletionEmbedding (𝕜 := 𝕜) (E := E))
      (e₂ := denseLinearIsometryRangeEmbedding f)
      (denseLinearIsometryCompletionEmbedding_denseRange (𝕜 := 𝕜) (E := E))
      (denseLinearIsometryRangeEmbedding_denseRange f h_dense)
      (denseLinearIsometryRangeEquiv_norm f)
      x)

end

end MathlibAnalytic
end MGAP4D
