import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalLinearIsometry
import Mathlib.Algebra.Algebra.Hom

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Diagonal complexification, bundled as a unital ring homomorphism between bounded
endomorphism rings. -/
noncomputable def diagonalComplexificationRingHom :
    (H →L[ℝ] H) →+*
      (StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) where
  toFun := diagonalComplexification
  map_zero' := diagonalComplexification_zero
  map_one' := diagonalComplexification_one
  map_add' := diagonalComplexification_add
  map_mul' := diagonalComplexification_mul

@[simp]
theorem diagonalComplexificationRingHom_apply (T : H →L[ℝ] H) :
    diagonalComplexificationRingHom T = diagonalComplexification T :=
  rfl

/-- Diagonal complexification, bundled as a real algebra homomorphism between bounded
endomorphism algebras. -/
noncomputable def diagonalComplexificationAlgHom :
    (H →L[ℝ] H) →ₐ[ℝ]
      (StandardRealHilbertComplexification H →L[ℂ]
        StandardRealHilbertComplexification H) :=
  AlgHom.mk' diagonalComplexificationRingHom fun r T =>
    diagonalComplexification_smul_real r T

@[simp]
theorem diagonalComplexificationAlgHom_apply (T : H →L[ℝ] H) :
    diagonalComplexificationAlgHom T = diagonalComplexification T :=
  rfl

@[simp]
theorem diagonalComplexificationAlgHom_toRingHom :
    (diagonalComplexificationAlgHom (H := H) :
      (H →L[ℝ] H) →+*
        (StandardRealHilbertComplexification H →L[ℂ]
          StandardRealHilbertComplexification H)) =
      diagonalComplexificationRingHom :=
  rfl

/-- The real algebra homomorphism furnished by diagonal complexification is injective. -/
theorem diagonalComplexificationAlgHom_injective :
    Function.Injective (diagonalComplexificationAlgHom (H := H)) :=
  diagonalComplexificationLinearIsometry.injective

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
