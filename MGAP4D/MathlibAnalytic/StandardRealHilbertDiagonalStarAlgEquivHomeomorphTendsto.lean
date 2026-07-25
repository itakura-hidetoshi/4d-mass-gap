import MGAP4D.MathlibAnalytic.StandardRealHilbertDiagonalStarAlgEquivHomeomorphMetric

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace StandardRealHilbertComplexification

variable {H : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/--
Convergence through diagonal complexification is equivalent to convergence before
complexification, for an arbitrary source filter.

The arbitrary-filter formulation applies uniformly to sequences, subnets, finite-volume
limits, and other directed approximation systems.
-/
@[simp]
theorem tendsto_diagonalComplexificationStarAlgEquivHomeomorph_iff
    {ι : Type*} {l : Filter ι} (f : ι → H →L[ℝ] H) (T : H →L[ℝ] H) :
    Tendsto
        (fun i => diagonalComplexificationStarAlgEquivHomeomorph (H := H) (f i))
        l
        (𝓝 (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T)) ↔
      Tendsto f l (𝓝 T) := by
  constructor
  · intro h
    have h' :=
      ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm.continuous.tendsto
        (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T)).comp h
    simpa using h'
  · intro h
    exact
      ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).continuous.tendsto T).comp h

/--
Convergence through the inverse diagonal complexification homeomorphism is equivalent to
convergence in the diagonal star-subalgebra, for an arbitrary source filter.
-/
@[simp]
theorem tendsto_diagonalComplexificationStarAlgEquivHomeomorph_symm_iff
    {ι : Type*} {l : Filter ι}
    (f : ι → diagonalComplexificationStarSubalgebra (H := H))
    (S : diagonalComplexificationStarSubalgebra (H := H)) :
    Tendsto
        (fun i => (diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm (f i))
        l
        (𝓝 ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm S)) ↔
      Tendsto f l (𝓝 S) := by
  constructor
  · intro h
    have h' :=
      ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).continuous.tendsto
        ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm S)).comp h
    simpa using h'
  · intro h
    exact
      ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm.continuous.tendsto S).comp h

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
