import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalAlgHom
import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalAdjointPreservation
import Mathlib.Algebra.Star.StarAlgHom

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Diagonal complexification, bundled as a real star algebra homomorphism between bounded
endomorphism algebras. -/
noncomputable def diagonalComplexificationStarAlgHom :
    (H →L[ℝ] H) →⋆ₐ[ℝ]
      (StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) where
  toAlgHom := diagonalComplexificationAlgHom
  map_star' := diagonalComplexification_star

@[simp]
theorem diagonalComplexificationStarAlgHom_apply (T : H →L[ℝ] H) :
    diagonalComplexificationStarAlgHom T = diagonalComplexification T :=
  rfl

@[simp]
theorem diagonalComplexificationStarAlgHom_toAlgHom :
    (diagonalComplexificationStarAlgHom (H := H) :
      (H →L[ℝ] H) →ₐ[ℝ]
        (StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H)) =
      diagonalComplexificationAlgHom :=
  rfl

/-- The real star algebra homomorphism furnished by diagonal complexification is injective. -/
theorem diagonalComplexificationStarAlgHom_injective :
    Function.Injective (diagonalComplexificationStarAlgHom (H := H)) :=
  diagonalComplexificationLinearIsometry.injective

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
