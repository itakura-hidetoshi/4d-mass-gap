import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalComplexification
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace InnerProduct

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Diagonal complexification commutes with the Hilbert-space adjoint. -/
@[simp]
theorem diagonalComplexification_adjoint (T : H →L[ℝ] H) :
    diagonalComplexification (T†) = (diagonalComplexification T)† := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro z w
  apply Complex.ext <;>
    simp [inner_apply, standardInner, ContinuousLinearMap.adjoint_inner_left]

/-- Diagonal complexification preserves the star operation on bounded endomorphisms. -/
@[simp]
theorem diagonalComplexification_star (T : H →L[ℝ] H) :
    diagonalComplexification (star T) = star (diagonalComplexification T) := by
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint]
  exact diagonalComplexification_adjoint T

/-- A self-adjoint real operator remains self-adjoint after diagonal complexification. -/
theorem diagonalComplexification_isSelfAdjoint
    {T : H →L[ℝ] H} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (diagonalComplexification T) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at hT ⊢
  calc
    (diagonalComplexification T)† = diagonalComplexification (T†) :=
      (diagonalComplexification_adjoint T).symm
    _ = diagonalComplexification T := congrArg diagonalComplexification hT

end StandardRealHilbertComplexification

end

end MathlibAnalytic
end MGAP4D
