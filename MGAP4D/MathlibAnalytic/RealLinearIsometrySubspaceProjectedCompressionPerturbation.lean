import MGAP4D.MathlibAnalytic.RealLinearIsometrySubspaceProjectedCompression
import Mathlib.Tactic

noncomputable section

namespace MGAP4D
namespace MathlibAnalytic

variable {H B : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup B] [InnerProductSpace ℝ B]

/-- For fixed isometric embedding and fixed projected subspace, projected
compression is additive in the compressed operator. -/
theorem realLinearIsometrySubspaceProjectedCompression_sub
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H) [CompleteSpace M]
    (T U : H →L[ℝ] H) :
    realLinearIsometrySubspaceProjectedCompression J M T -
        realLinearIsometrySubspaceProjectedCompression J M U =
      realLinearIsometrySubspaceProjectedCompression J M (T - U) := by
  ext y
  simp [realLinearIsometrySubspaceProjectedCompression]

/-- Projected compression is 1-Lipschitz in operator norm when the embedding
and projected physical subspace are held fixed. -/
theorem realLinearIsometrySubspaceProjectedCompression_norm_sub_le
    (J : H →ₗᵢ[ℝ] B)
    (M : Submodule ℝ H) [CompleteSpace M]
    (T U : H →L[ℝ] H) :
    ‖realLinearIsometrySubspaceProjectedCompression J M T -
        realLinearIsometrySubspaceProjectedCompression J M U‖ ≤
      ‖T - U‖ := by
  rw [realLinearIsometrySubspaceProjectedCompression_sub]
  exact
    realLinearIsometrySubspaceProjectedCompression_opNorm_le
      J M (T - U) ‖T - U‖ (norm_nonneg _)
      (fun x _hx => (T - U).le_opNorm x)

end MathlibAnalytic
end MGAP4D
