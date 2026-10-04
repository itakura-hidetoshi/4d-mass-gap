import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompression
import MGAP4D.MathlibAnalytic.RealLinearIsometryProjectedInversePythagoras
import Mathlib.Tactic

/-!
# Subspace-projected isometric compression as an orthogonal projection

Let `J : H -> B` be a real linear isometric embedding and let `M` be a
complete Hilbert subspace of `H`.

The operator

  J ∘ P_M ∘ J^{-1}_proj

is exactly the orthogonal projection in `B` onto the embedded subspace
`M.map J.toLinearMap`.

This identifies the identity-instance of
`realLinearIsometrySubspaceProjectedCompression` with Mathlib's canonical
`starProjection`.  The result is model-independent and provides the direct
conditional-expectation/projection interface used by the finite Yang--Mills
reconstruction geometry.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {H B : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- The embedded image of a complete Hilbert subspace under a real linear
isometry is complete. -/
noncomputable instance realLinearIsometrySubspaceMapCompleteSpace
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H)
    [CompleteSpace M] :
    CompleteSpace (M.map J.toLinearMap) := by
  exact J.completeSpace_map M

/-- Identity subspace-projected compression is exactly the canonical orthogonal
projection onto the embedded subspace. -/
theorem realLinearIsometrySubspaceProjectedCompression_one_eq_starProjection_map
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H)
    [CompleteSpace M] :
    realLinearIsometrySubspaceProjectedCompression
        J M (1 : H →L[ℝ] H) =
      (M.map J.toLinearMap).starProjection := by
  apply ContinuousLinearMap.ext
  intro y
  let x : H := realLinearIsometryProjectedInverse J y
  let z : H := realHilbertSubspaceProjection M x
  let K : Submodule ℝ B := M.map J.toLinearMap
  have hzM : z ∈ M := by
    dsimp [z]
    change M.starProjection x ∈ M
    have hrange : M.starProjection x ∈ M.starProjection.range := ⟨x, rfl⟩
    simpa using hrange
  have hJzK : J z ∈ K := by
    exact ⟨z, hzM, rfl⟩
  have hxRange :
      J x = realHilbertSubspaceProjection (realLinearIsometryRange J) y := by
    dsimp [x]
    exact realLinearIsometry_map_projectedInverse_eq_rangeProjection J y
  have hRangeResidual :
      y - J x ∈ (realLinearIsometryRange J)ᗮ := by
    rw [hxRange]
    simpa [realHilbertSubspaceProjection] using
      (realLinearIsometryRange J).sub_starProjection_mem_orthogonal y
  have hMResidual : x - z ∈ Mᗮ := by
    dsimp [z]
    simpa [realHilbertSubspaceProjection] using
      M.sub_starProjection_mem_orthogonal x
  have hResidualK : y - J z ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rcases hw with ⟨m, hm, rfl⟩
    have hJmRange : J m ∈ realLinearIsometryRange J := ⟨m, rfl⟩
    have hfirst : inner ℝ (J m) (y - J x) = 0 :=
      (Submodule.mem_orthogonal (realLinearIsometryRange J) (y - J x)).1
        hRangeResidual (J m) hJmRange
    have hsecond : inner ℝ (J m) (J (x - z)) = 0 := by
      calc
        inner ℝ (J m) (J (x - z)) = inner ℝ m (x - z) :=
          J.inner_map_map m (x - z)
        _ = 0 :=
          (Submodule.mem_orthogonal M (x - z)).1 hMResidual m hm
    have hdecomp :
        y - J z = (y - J x) + J (x - z) := by
      rw [J.map_sub]
      abel
    rw [hdecomp, inner_add_right, hfirst, hsecond, add_zero]
  change J z = K.starProjection y
  exact
    Submodule.eq_starProjection_of_mem_orthogonal
      (K := K) hJzK hResidualK

/-- Pythagoras for identity subspace-projected compression, expressed directly
on the ambient Hilbert carrier. -/
theorem realLinearIsometrySubspaceProjectedCompression_one_residual_norm_sq_eq
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H)
    [CompleteSpace M]
    (y : B) :
    ‖y -
        realLinearIsometrySubspaceProjectedCompression
          J M (1 : H →L[ℝ] H) y‖ ^ 2 =
      ‖y‖ ^ 2 -
        ‖realLinearIsometrySubspaceProjectedCompression
          J M (1 : H →L[ℝ] H) y‖ ^ 2 := by
  rw [
    realLinearIsometrySubspaceProjectedCompression_one_eq_starProjection_map
      J M]
  have h :=
    realHilbertSubspaceProjection_sub_norm_sq_eq
      (M.map J.toLinearMap) y
  change
    ‖y - (M.map J.toLinearMap).starProjection y‖ ^ 2 =
      ‖y‖ ^ 2 - ‖(M.map J.toLinearMap).starProjection y‖ ^ 2
  rw [norm_sub_rev]
  simpa [realHilbertSubspaceProjection] using h

end

end MathlibAnalytic
end MGAP4D
