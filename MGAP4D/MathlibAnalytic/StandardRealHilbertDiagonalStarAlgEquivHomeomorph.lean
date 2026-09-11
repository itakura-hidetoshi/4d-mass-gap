import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquivIsometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
The diagonal complexification star-algebra equivalence, bundled as a homeomorphism.

This packages the already-proved forward and inverse continuity into the standard
Mathlib topological equivalence interface, so downstream spectral and limit
arguments can transport open, closed, compact, and convergent structures without
re-proving continuity.
-/
def diagonalComplexificationStarAlgEquivHomeomorph :
    (H →L[ℝ] H) ≃ₜ diagonalComplexificationStarSubalgebra (H := H) where
  toEquiv := (diagonalComplexificationStarAlgEquiv (H := H)).toEquiv
  continuous_toFun := diagonalComplexificationStarAlgEquiv_continuous (H := H)
  continuous_invFun := diagonalComplexificationStarAlgEquiv_symm_continuous (H := H)

@[simp]
theorem diagonalComplexificationStarAlgEquivHomeomorph_apply (T : H →L[ℝ] H) :
    diagonalComplexificationStarAlgEquivHomeomorph (H := H) T =
      diagonalComplexificationStarAlgEquiv (H := H) T :=
  rfl

@[simp]
theorem diagonalComplexificationStarAlgEquivHomeomorph_symm_apply
    (S : diagonalComplexificationStarSubalgebra (H := H)) :
    (diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm S =
      (diagonalComplexificationStarAlgEquiv (H := H)).symm S :=
  rfl

/-- The bundled homeomorphism is still an isometry. -/
theorem diagonalComplexificationStarAlgEquivHomeomorph_isometry :
    Isometry (diagonalComplexificationStarAlgEquivHomeomorph (H := H)) := by
  simpa only [diagonalComplexificationStarAlgEquivHomeomorph_apply] using
    diagonalComplexificationStarAlgEquiv_isometry (H := H)

/-- The inverse bundled homeomorphism is still an isometry. -/
theorem diagonalComplexificationStarAlgEquivHomeomorph_symm_isometry :
    Isometry ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm) := by
  simpa only [diagonalComplexificationStarAlgEquivHomeomorph_symm_apply] using
    diagonalComplexificationStarAlgEquiv_symm_isometry (H := H)

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
