import MGAP4D.MathlibAnalytic.R2MPrefixCauchySchwarz
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticExpansion
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedSeminormCandidate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pure real-analysis bridge from Cauchy--Schwarz to the sharp quadratic
Minkowski square bound.  This is intentionally phrased over real numbers before
being transported to the concrete finite-prefix graph-pair energy surface. -/
theorem real_add_two_mul_le_sqrt_add_sq_of_sq_le_mul
    (a b i : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcs : i ^ 2 ≤ a * b) :
    a + (2 : ℝ) * i + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
  let r : ℝ := Real.sqrt a * Real.sqrt b
  have hr_nonneg : 0 ≤ r := by
    exact mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have hr_sq : r ^ 2 = a * b := by
    dsimp [r]
    rw [mul_pow]
    rw [Real.sq_sqrt ha]
    rw [Real.sq_sqrt hb]
  have hi_le_r : i ≤ r := by
    by_cases hi_nonpos : i ≤ 0
    · exact le_trans hi_nonpos hr_nonneg
    · have hi_pos : 0 < i := lt_of_not_ge hi_nonpos
      have hsq : i ^ 2 ≤ r ^ 2 := by
        simpa [hr_sq] using hcs
      by_contra hnot
      have hr_lt_i : r < i := lt_of_not_ge hnot
      nlinarith
  calc
    a + (2 : ℝ) * i + b ≤ a + (2 : ℝ) * r + b := by
      nlinarith
    _ = (Real.sqrt a + Real.sqrt b) ^ 2 := by
      dsimp [r]
      rw [add_sq]
      rw [Real.sq_sqrt ha]
      rw [Real.sq_sqrt hb]
      ring

/-- Finite-prefix Minkowski square bound for the concrete bounded graph-pair
energy quadratic.  This is the sharp square-level consequence of the formal
finite-prefix Cauchy--Schwarz theorem. -/
theorem r2m_prefix_minkowski_square
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N
        (concreteL2GraphPairPrefixEnergyBoundedAdd x y) ≤
      (concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N x +
        concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate N y) ^ 2 := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_quadratic_add_expansion N x y]
  unfold concreteL2GraphPairPrefixEnergyBoundedSeminormCandidate
  exact real_add_two_mul_le_sqrt_add_sq_of_sq_le_mul
    (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x)
    (concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y)
    (concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y)
    (concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg N x)
    (concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg N y)
    (r2m_prefix_cauchy_schwarz N x y)

end

end MathlibAnalytic
end MGAP4D
