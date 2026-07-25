import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquivHomeomorphTendsto
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

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
  let e := diagonalComplexificationStarAlgEquivHomeomorph (H := H)
  constructor
  · intro h
    change CauchySeq (fun n => e (f n)) at h
    have h' :=
      diagonalComplexificationStarAlgEquivHomeomorph_symm_isometry
        (H := H) |>.lipschitz.cauchySeq_comp h
    change CauchySeq (fun n => e.symm (e (f n))) at h'
    simpa only [e.symm_apply_apply] using h'
  · intro h
    exact
      diagonalComplexificationStarAlgEquivHomeomorph_isometry
        (H := H) |>.lipschitz.cauchySeq_comp h

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
  let e := diagonalComplexificationStarAlgEquivHomeomorph (H := H)
  constructor
  · intro h
    change CauchySeq (fun n => e.symm (f n)) at h
    have h' :=
      diagonalComplexificationStarAlgEquivHomeomorph_isometry
        (H := H) |>.lipschitz.cauchySeq_comp h
    change CauchySeq (fun n => e (e.symm (f n))) at h'
    simpa only [e.apply_symm_apply] using h'
  · intro h
    exact
      diagonalComplexificationStarAlgEquivHomeomorph_symm_isometry
        (H := H) |>.lipschitz.cauchySeq_comp h

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
