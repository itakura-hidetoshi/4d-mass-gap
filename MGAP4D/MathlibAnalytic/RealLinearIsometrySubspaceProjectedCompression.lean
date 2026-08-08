import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedCompression

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

variable {H B : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- Orthogonal projection onto a complete real Hilbert subspace, regarded as
an ambient continuous linear endomorphism. -/
noncomputable def realHilbertSubspaceProjection
    (M : Submodule ℝ H) [CompleteSpace M] : H →L[ℝ] H :=
  M.subtypeL.comp M.orthogonalProjection

/-- The ambient projection is the identity on the chosen subspace. -/
@[simp] theorem realHilbertSubspaceProjection_apply_mem
    (M : Submodule ℝ H) [CompleteSpace M]
    (x : H) (hx : x ∈ M) :
    realHilbertSubspaceProjection M x = x := by
  change ((M.orthogonalProjection x : M) : H) = x
  simpa using M.orthogonalProjection_mem_subspace_eq_self ⟨x, hx⟩

/-- Orthogonal projection to a complete Hilbert subspace is contractive. -/
theorem realHilbertSubspaceProjection_norm_le
    (M : Submodule ℝ H) [CompleteSpace M]
    (x : H) :
    ‖realHilbertSubspaceProjection M x‖ ≤ ‖x‖ := by
  change ‖(M.orthogonalProjection x : M)‖ ≤ ‖x‖
  exact M.norm_orthogonalProjection_apply_le x

/-- Project an ambient boundary vector to the isometric physical range, pull it
back to the physical Hilbert space, project to a distinguished complete
subspace, apply `T`, and embed again.

Concretely:
`J ∘ T ∘ P_M ∘ J⁻¹ ∘ P_(range J)`.

This is the correct whole-ambient extension for a transfer operator whose
strict estimate is known only on a physical sector such as the
vacuum-orthogonal subspace. -/
noncomputable def realLinearIsometrySubspaceProjectedCompression
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H) [CompleteSpace M]
    (T : H →L[ℝ] H) : B →L[ℝ] B :=
  J.toContinuousLinearMap.comp
    (T.comp
      ((realHilbertSubspaceProjection M).comp
        (realLinearIsometryProjectedInverse J)))

/-- On vectors already lying in the distinguished physical subspace, the
subspace-projected compression is exact conjugation by `J`. -/
@[simp] theorem realLinearIsometrySubspaceProjectedCompression_apply_map_mem
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H) [CompleteSpace M]
    (T : H →L[ℝ] H)
    (x : H) (hx : x ∈ M) :
    realLinearIsometrySubspaceProjectedCompression J M T (J x) = J (T x) := by
  simp [realLinearIsometrySubspaceProjectedCompression,
    realHilbertSubspaceProjection_apply_mem M x hx]

/-- A pointwise contraction of `T` on the distinguished subspace transfers to
all ambient vectors; both orthogonal projections and the isometric pullback
cost no additional norm factor. -/
theorem realLinearIsometrySubspaceProjectedCompression_norm_le
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H) [CompleteSpace M]
    (T : H →L[ℝ] H)
    (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ x : H, x ∈ M → ‖T x‖ ≤ c * ‖x‖)
    (y : B) :
    ‖realLinearIsometrySubspaceProjectedCompression J M T y‖ ≤ c * ‖y‖ := by
  let x := realLinearIsometryProjectedInverse J y
  let z := realHilbertSubspaceProjection M x
  have hz : z ∈ M := by
    change ((M.orthogonalProjection x : M) : H) ∈ M
    exact (M.orthogonalProjection x).property
  change ‖J (T z)‖ ≤ c * ‖y‖
  rw [J.norm_map]
  calc
    ‖T z‖ ≤ c * ‖z‖ := hT z hz
    _ ≤ c * ‖x‖ := by
      exact mul_le_mul_of_nonneg_left
        (realHilbertSubspaceProjection_norm_le M x) hc
    _ ≤ c * ‖y‖ := by
      exact mul_le_mul_of_nonneg_left
        (realLinearIsometryProjectedInverse_norm_le J y) hc

/-- The corresponding ambient operator norm is bounded by the same sector
constant. -/
theorem realLinearIsometrySubspaceProjectedCompression_opNorm_le
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H) [CompleteSpace M]
    (T : H →L[ℝ] H)
    (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ x : H, x ∈ M → ‖T x‖ ≤ c * ‖x‖) :
    ‖realLinearIsometrySubspaceProjectedCompression J M T‖ ≤ c := by
  exact ContinuousLinearMap.opNorm_le_bound _ hc
    (realLinearIsometrySubspaceProjectedCompression_norm_le J M T c hc hT)

end MathlibAnalytic
end MGAP4D

end
