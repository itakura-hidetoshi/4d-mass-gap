import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompression
import Mathlib.Tactic

/-!
# Pythagorean identities for projected isometric reconstruction

For a real linear isometric embedding `J : H -> B`, the canonical projected
inverse first orthogonally projects an ambient vector onto `range J` and then
uses the inverse isometry.  Consequently the reconstruction defect is exactly
the orthogonal-projection residual.

This file records two model-independent identities:

* projection onto a complete Hilbert subspace loses exactly the squared norm of
  the orthogonal residual;
* reconstructing through a linear isometry satisfies

    ||J (R_J y) - y||^2 = ||y||^2 - ||R_J y||^2.

These are the Hilbert-space forms needed to reinterpret finite Yang--Mills
reconstruction residuals as conditional-variance / norm-loss quantities.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

variable {H B : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]

section CompleteSource

variable [CompleteSpace H]

/-- The canonical projected inverse, re-embedded into the ambient Hilbert
space, is exactly the orthogonal projection onto the isometry range. -/
theorem realLinearIsometry_map_projectedInverse_eq_rangeProjection
    (J : H →ₗᵢ[ℝ] B)
    (y : B) :
    J (realLinearIsometryProjectedInverse J y) =
      realHilbertSubspaceProjection (realLinearIsometryRange J) y := by
  unfold realLinearIsometryProjectedInverse
  unfold realHilbertSubspaceProjection
  change
    J
        (J.equivRange.symm
          ((realLinearIsometryRange J).orthogonalProjection y)) =
      (((realLinearIsometryRange J).orthogonalProjection y :
          realLinearIsometryRange J) : B)
  change
    ((J.equivRange
          (J.equivRange.symm
            ((realLinearIsometryRange J).orthogonalProjection y)) :
        realLinearIsometryRange J) : B) =
      (((realLinearIsometryRange J).orthogonalProjection y :
          realLinearIsometryRange J) : B)
  rw [J.equivRange.apply_symm_apply]

end CompleteSource

/-- Pythagoras for the residual of orthogonal projection onto a complete real
Hilbert subspace.  Ambient completeness is not needed; completeness of the
projected subspace is sufficient. -/
theorem realHilbertSubspaceProjection_sub_norm_sq_eq
    (M : Submodule ℝ H)
    [CompleteSpace M]
    (x : H) :
    ‖realHilbertSubspaceProjection M x - x‖ ^ 2 =
      ‖x‖ ^ 2 - ‖realHilbertSubspaceProjection M x‖ ^ 2 := by
  change ‖M.starProjection x - x‖ ^ 2 =
    ‖x‖ ^ 2 - ‖M.starProjection x‖ ^ 2
  have hsplit := M.starProjection_add_starProjection_orthogonal x
  have hresidual :
      M.starProjection x - x = -(Mᗮ.starProjection x) := by
    calc
      M.starProjection x - x =
          M.starProjection x -
            (M.starProjection x + Mᗮ.starProjection x) := by
              rw [hsplit]
      _ = -(Mᗮ.starProjection x) := by
        abel
  rw [hresidual, norm_neg]
  have hpyth := M.norm_sq_eq_add_norm_sq_starProjection x
  nlinarith

section CompleteSource

variable [CompleteSpace H]

/-- The reconstruction residual of a real linear isometry is exactly the
squared norm lost by its canonical projected inverse.

The proof uses Pythagoras directly on `range J`.  It deliberately does not
ask for `CompleteSpace B`: completeness of the isometric range follows from
the complete source `H`, which is precisely the hypothesis needed by the
canonical projected inverse. -/
theorem realLinearIsometry_projectedInverse_residual_norm_sq_eq
    (J : H →ₗᵢ[ℝ] B)
    (y : B) :
    ‖J (realLinearIsometryProjectedInverse J y) - y‖ ^ 2 =
      ‖y‖ ^ 2 - ‖realLinearIsometryProjectedInverse J y‖ ^ 2 := by
  let K : Submodule ℝ B := realLinearIsometryRange J
  have hmap :
      J (realLinearIsometryProjectedInverse J y) = K.starProjection y := by
    simpa [K, realHilbertSubspaceProjection] using
      realLinearIsometry_map_projectedInverse_eq_rangeProjection J y
  have hsplit : K.starProjection y + Kᗮ.starProjection y = y :=
    K.starProjection_add_starProjection_orthogonal y
  have hresidual :
      J (realLinearIsometryProjectedInverse J y) - y =
        -(Kᗮ.starProjection y) := by
    rw [hmap]
    calc
      K.starProjection y - y =
          K.starProjection y -
            (K.starProjection y + Kᗮ.starProjection y) := by
              rw [hsplit]
      _ = -(Kᗮ.starProjection y) := by
        abel
  have hprojNorm :
      ‖K.starProjection y‖ =
        ‖realLinearIsometryProjectedInverse J y‖ := by
    rw [← hmap]
    exact J.norm_map _
  have hpyth := K.norm_sq_eq_add_norm_sq_starProjection y
  rw [hprojNorm] at hpyth
  rw [hresidual, norm_neg]
  nlinarith

/-- The squared reconstruction defect is automatically nonnegative in its
norm-loss form. -/
theorem realLinearIsometry_projectedInverse_norm_sq_le
    (J : H →ₗᵢ[ℝ] B)
    (y : B) :
    ‖realLinearIsometryProjectedInverse J y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have h :=
    realLinearIsometry_projectedInverse_residual_norm_sq_eq J y
  nlinarith [sq_nonneg ‖J (realLinearIsometryProjectedInverse J y) - y‖]

end CompleteSource

end

end MathlibAnalytic
end MGAP4D
