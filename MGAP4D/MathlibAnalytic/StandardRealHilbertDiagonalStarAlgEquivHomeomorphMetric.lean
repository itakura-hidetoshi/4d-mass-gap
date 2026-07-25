import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquivHomeomorph

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The diagonal complexification homeomorphism preserves distance. -/
@[simp]
theorem dist_diagonalComplexificationStarAlgEquivHomeomorph_apply
    (S T : H →L[ℝ] H) :
    dist (diagonalComplexificationStarAlgEquivHomeomorph (H := H) S)
        (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T) =
      dist S T :=
  diagonalComplexificationStarAlgEquivHomeomorph_isometry.dist_eq S T

/-- The inverse diagonal complexification homeomorphism preserves distance. -/
@[simp]
theorem dist_diagonalComplexificationStarAlgEquivHomeomorph_symm_apply
    (S T : diagonalComplexificationStarSubalgebra (H := H)) :
    dist ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm S)
        ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm T) =
      dist S T :=
  diagonalComplexificationStarAlgEquivHomeomorph_symm_isometry.dist_eq S T

/-- The diagonal complexification homeomorphism preserves extended distance. -/
@[simp]
theorem edist_diagonalComplexificationStarAlgEquivHomeomorph_apply
    (S T : H →L[ℝ] H) :
    edist (diagonalComplexificationStarAlgEquivHomeomorph (H := H) S)
        (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T) =
      edist S T :=
  diagonalComplexificationStarAlgEquivHomeomorph_isometry.edist_eq S T

/-- The inverse diagonal complexification homeomorphism preserves extended distance. -/
@[simp]
theorem edist_diagonalComplexificationStarAlgEquivHomeomorph_symm_apply
    (S T : diagonalComplexificationStarSubalgebra (H := H)) :
    edist ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm S)
        ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm T) =
      edist S T :=
  diagonalComplexificationStarAlgEquivHomeomorph_symm_isometry.edist_eq S T

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
