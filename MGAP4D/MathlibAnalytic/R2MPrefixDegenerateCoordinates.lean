import MGAP4D.MathlibAnalytic.R2MPrefixDegenerateKernel

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- If one graph-pair energy term vanishes, both concrete coordinates vanish at
that index. -/
theorem r2m_energy_term_zero_coordinates
    (p : ConcreteL2GraphPairSpace) (n : ℕ)
    (h : concreteL2GraphPairEnergyTerm p n = 0) :
    (concreteL2GraphPairFst p).1 n = 0 ∧
      (concreteL2GraphPairSnd p).1 n = 0 := by
  unfold concreteL2GraphPairEnergyTerm at h
  have hf_nonneg : 0 ≤ (concreteL2GraphPairFst p).1 n ^ 2 := sq_nonneg _
  have hs_nonneg : 0 ≤ (concreteL2GraphPairSnd p).1 n ^ 2 := sq_nonneg _
  have hf_sq_zero : (concreteL2GraphPairFst p).1 n ^ 2 = 0 := by
    nlinarith
  have hs_sq_zero : (concreteL2GraphPairSnd p).1 n ^ 2 = 0 := by
    nlinarith
  exact And.intro (sq_eq_zero_iff.mp hf_sq_zero) (sq_eq_zero_iff.mp hs_sq_zero)

/-- If a finite graph-pair energy prefix is zero, every coordinate inside the
prefix is zero. -/
theorem r2m_prefix_zero_coordinates
    (N : ℕ) (p : ConcreteL2GraphPairSpace)
    (h : concreteL2GraphPairEnergyPrefix N p = 0) :
    ∀ n ∈ Finset.range N,
      (concreteL2GraphPairFst p).1 n = 0 ∧
        (concreteL2GraphPairSnd p).1 n = 0 := by
  intro n hn
  exact r2m_energy_term_zero_coordinates p n
    (r2m_prefix_energy_term_eq_zero_of_prefix_zero N p h n hn)

end

end MathlibAnalytic
end MGAP4D
