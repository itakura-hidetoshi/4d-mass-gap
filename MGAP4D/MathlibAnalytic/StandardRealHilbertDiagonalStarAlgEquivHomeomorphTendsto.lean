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
    Filter.Tendsto
        (fun i => diagonalComplexificationStarAlgEquivHomeomorph (H := H) (f i))
        l
        (nhds (diagonalComplexificationStarAlgEquivHomeomorph (H := H) T)) ↔
      Filter.Tendsto f l (nhds T) := by
  let e := diagonalComplexificationStarAlgEquivHomeomorph (H := H)
  constructor
  · intro h
    change Filter.Tendsto (fun i => e (f i)) l (nhds (e T)) at h
    have h' := (e.symm.continuous.tendsto (e T)).comp h
    simpa only [Function.comp_apply, e.symm_apply_apply] using h'
  · intro h
    exact (e.continuous.tendsto T).comp h

/--
Convergence through the inverse diagonal complexification homeomorphism is equivalent to
convergence in the diagonal star-subalgebra, for an arbitrary source filter.
-/
@[simp]
theorem tendsto_diagonalComplexificationStarAlgEquivHomeomorph_symm_iff
    {ι : Type*} {l : Filter ι}
    (f : ι → diagonalComplexificationStarSubalgebra (H := H))
    (S : diagonalComplexificationStarSubalgebra (H := H)) :
    Filter.Tendsto
        (fun i => (diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm (f i))
        l
        (nhds ((diagonalComplexificationStarAlgEquivHomeomorph (H := H)).symm S)) ↔
      Filter.Tendsto f l (nhds S) := by
  let e := diagonalComplexificationStarAlgEquivHomeomorph (H := H)
  constructor
  · intro h
    change Filter.Tendsto (fun i => e.symm (f i)) l (nhds (e.symm S)) at h
    have h' := (e.continuous.tendsto (e.symm S)).comp h
    simpa only [Function.comp_apply, e.apply_symm_apply] using h'
  · intro h
    exact (e.symm.continuous.tendsto S).comp h

end StandardRealHilbertComplexification

end
end MathlibAnalytic
end MGAP4D
