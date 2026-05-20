import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProduct

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite-sum algebra used by the bounded-prefix quadratic expansion. -/
theorem concrete_l2_graph_pair_prefix_sum_mixed_sq_expansion
    (N : ℕ) (a b : ℕ → ℝ) :
    (∑ n in Finset.range N, (a n * b n * 2 + a n ^ 2 + b n ^ 2)) =
      (∑ n in Finset.range N, a n ^ 2) +
        (∑ n in Finset.range N, a n * b n) * 2 +
          (∑ n in Finset.range N, b n ^ 2) := by
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_mul]
  ring

/-- The same finite-sum algebra with the cross term written first, matching the
normal form produced by `ring_nf` after expanding `(a+b)^2`. -/
theorem concrete_l2_graph_pair_prefix_sum_cross_first_expansion
    (N : ℕ) (a b : ℕ → ℝ) :
    (∑ n in Finset.range N, (a n * b n * 2 + a n ^ 2 + b n ^ 2)) =
      (∑ n in Finset.range N, a n ^ 2) +
        (∑ n in Finset.range N, a n * b n) * 2 +
          (∑ n in Finset.range N, b n ^ 2) := by
  exact concrete_l2_graph_pair_prefix_sum_mixed_sq_expansion N a b

end

end MathlibAnalytic
end MGAP4D
