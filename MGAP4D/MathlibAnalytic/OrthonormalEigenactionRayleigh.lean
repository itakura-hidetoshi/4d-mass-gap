import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapOrthonormalEigenbasisContraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A symmetric real operator that is diagonal on an orthonormal basis has the
expected Rayleigh spectral expansion. -/
theorem rayleigh_eq_sum_of_orthonormal_eigenaction
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (T : E →L[ℝ] E)
    (a : ι → ℝ)
    (hT : ∀ x y : E, inner ℝ (T x) y = inner ℝ (T y) x)
    (hEigen : ∀ i : ι, T (b i) = a i • b i)
    (x : E) :
    inner ℝ (T x) x =
      ∑ i : ι, (inner ℝ (b i) x) ^ 2 * a i := by
  calc
    inner ℝ (T x) x =
        ∑ i : ι, inner ℝ (T x) (b i) * inner ℝ (b i) x :=
      (b.sum_inner_mul_inner (T x) x).symm
    _ = ∑ i : ι, (inner ℝ (b i) x) ^ 2 * a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hT x (b i), hEigen i, real_inner_smul_left]
      ring

end

end MathlibAnalytic
end MGAP4D
