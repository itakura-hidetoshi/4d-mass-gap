import MGAP4D.MathlibAnalytic.R2MPrefixMinkowskiSquare

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-prefix triangle inequality for the concrete bounded graph-pair
seminorm candidate.  This is obtained from the sharp Minkowski square bound by
mathlib's monotonicity of `Real.sqrt` and the nonnegativity of the right-hand
side. -/
theorem r2m_prefix_triangle_inequality
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x +
        concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y := by
  unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
  have hquad := r2m_prefix_minkowski_square N x y
  unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate at hquad
  have hsqrt := Real.sqrt_le_sqrt hquad
  have hright_nonneg :
      0 ≤ Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) +
        Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) := by
    exact add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright_sqrt :
      Real.sqrt
          ((Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) +
            Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y)) ^ 2) =
        Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) +
          Real.sqrt (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y) := by
    rw [Real.sqrt_sq_eq_abs]
    exact abs_of_nonneg hright_nonneg
  rwa [hright_sqrt] at hsqrt

end

end MathlibAnalytic
end MGAP4D
