import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquiv

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The bundled star-algebra equivalence preserves the operator norm. -/
@[simp]
theorem norm_diagonalComplexificationStarAlgEquiv_apply (T : H →L[ℝ] H) :
    ‖diagonalComplexificationStarAlgEquiv (H := H) T‖ = ‖T‖ := by
  change ‖diagonalComplexification T‖ = ‖T‖
  exact diagonalComplexificationLinearIsometry.norm_map T

/-- The bundled star-algebra equivalence is an isometry. -/
theorem diagonalComplexificationStarAlgEquiv_isometry :
    Isometry (diagonalComplexificationStarAlgEquiv (H := H)) := by
  intro S T
  change dist (diagonalComplexification S) (diagonalComplexification T) = dist S T
  exact diagonalComplexification_isometry S T

/-- The inverse bundled star-algebra equivalence preserves the operator norm. -/
@[simp]
theorem norm_diagonalComplexificationStarAlgEquiv_symm_apply
    (S : diagonalComplexificationStarSubalgebra (H := H)) :
    ‖(diagonalComplexificationStarAlgEquiv (H := H)).symm S‖ = ‖S‖ := by
  have h := norm_diagonalComplexificationStarAlgEquiv_apply
    (H := H) ((diagonalComplexificationStarAlgEquiv (H := H)).symm S)
  simpa using h.symm

/-- The inverse bundled star-algebra equivalence is an isometry. -/
theorem diagonalComplexificationStarAlgEquiv_symm_isometry :
    Isometry ((diagonalComplexificationStarAlgEquiv (H := H)).symm) := by
  intro S T
  have h := diagonalComplexificationStarAlgEquiv_isometry
    (H := H)
    ((diagonalComplexificationStarAlgEquiv (H := H)).symm S)
    ((diagonalComplexificationStarAlgEquiv (H := H)).symm T)
  simpa using h.symm

/-- The bundled star-algebra equivalence is continuous. -/
theorem diagonalComplexificationStarAlgEquiv_continuous :
    Continuous (diagonalComplexificationStarAlgEquiv (H := H)) :=
  diagonalComplexificationStarAlgEquiv_isometry.continuous

/-- The inverse bundled star-algebra equivalence is continuous. -/
theorem diagonalComplexificationStarAlgEquiv_symm_continuous :
    Continuous ((diagonalComplexificationStarAlgEquiv (H := H)).symm) :=
  diagonalComplexificationStarAlgEquiv_symm_isometry.continuous

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
