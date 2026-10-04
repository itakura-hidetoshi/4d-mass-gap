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
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]

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

/-- Pythagoras for the residual of orthogonal projection onto a complete real
Hilbert subspace. -/
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
    rw [← hsplit]
    abel
  rw [hresidual, norm_neg]
  have hpyth := M.norm_sq_eq_add_norm_sq_starProjection x
  nlinarith

/-- The reconstruction residual of a real linear isometry is exactly the
squared norm lost by its canonical projected inverse. -/
theorem realLinearIsometry_projectedInverse_residual_norm_sq_eq
    (J : H →ₗᵢ[ℝ] B)
    (y : B) :
    ‖J (realLinearIsometryProjectedInverse J y) - y‖ ^ 2 =
      ‖y‖ ^ 2 - ‖realLinearIsometryProjectedInverse J y‖ ^ 2 := by
  have hmap :=
    realLinearIsometry_map_projectedInverse_eq_rangeProjection J y
  have hproj :=
    realHilbertSubspaceProjection_sub_norm_sq_eq
      (realLinearIsometryRange J) y
  have hnorm :
      ‖realHilbertSubspaceProjection (realLinearIsometryRange J) y‖ =
        ‖realLinearIsometryProjectedInverse J y‖ := by
    calc
      ‖realHilbertSubspaceProjection (realLinearIsometryRange J) y‖ =
          ‖J (realLinearIsometryProjectedInverse J y)‖ := by
        rw [hmap]
      _ = ‖realLinearIsometryProjectedInverse J y‖ := J.norm_map _
  rw [hmap]
  rw [hnorm] at hproj
  exact hproj

/-- The squared reconstruction defect is automatically nonnegative in its
norm-loss form. -/
theorem realLinearIsometry_projectedInverse_norm_sq_le
    (J : H →ₗᵢ[ℝ] B)
    (y : B) :
    ‖realLinearIsometryProjectedInverse J y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  have h :=
    realLinearIsometry_projectedInverse_residual_norm_sq_eq J y
  nlinarith [sq_nonneg ‖J (realLinearIsometryProjectedInverse J y) - y‖]

end

end MathlibAnalytic
end MGAP4D
