import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefix

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- If a finite graph-pair energy prefix is zero, then every energy term inside
that prefix is zero.  This is the finite nonnegative-sum degeneracy kernel. -/
theorem r2m_prefix_energy_term_eq_zero_of_prefix_zero
    (N : ℕ) (p : ConcreteL2GraphPairSpace)
    (h : concreteL2GraphPairEnergyPrefix N p = 0) :
    ∀ n ∈ Finset.range N, concreteL2GraphPairEnergyTerm p n = 0 := by
  unfold concreteL2GraphPairEnergyPrefix at h
  rw [Finset.sum_eq_zero_iff_of_nonneg] at h
  · exact h
  · intro n _hn
    exact concrete_l2_graph_pair_energy_term_nonneg p n

end

end MathlibAnalytic
end MGAP4D
