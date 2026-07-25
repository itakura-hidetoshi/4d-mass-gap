import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquivHomeomorphTendsto

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
A sequence of real bounded endomorphisms is Cauchy exactly when its diagonal
complexification is Cauchy.
-/
@[simp]
theorem cauchySeq_diagonalComplexificationStarAlgEquivHomeomorph_iff
    (f : ℕ → H →L[ℝ] H) :
    CauchySeq
        (fun n => diagonalComplexificationStarAlgEquivHomeomorph (H := H) (f n)) ↔
      CauchySeq f := by
  simpa only [Metric.cauchySeq_iff,
    dist_diagonalComplexificationStarAlgEquivHomeomorph_apply]

/--
A sequence in the diagonal star-subalgebra is Cauchy exactly when its inverse image
under diagonal complexification is Cauchy.
-/
@[simp]
theorem cauchySeq_diagonalComplexificationStarAlgEquivHomeomorph_symm_iff
    (f : ℕ → diagonalComplexificationStarSubalgebra (H := H)) :
    CauchySeq
        (fun n => (diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm (f n)) ↔
      CauchySeq f := by
  simpa only [Metric.cauchySeq_iff,
    dist_diagonalComplexificationStarAlgEquivHomeomorph_symm_apply]

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
