import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotone

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite-prefix additive energy estimate expressed directly in prefix form.
The proof uses mathlib finite-sum algebra: `Finset.sum_add_distrib` and
`Finset.smul_sum`. -/
theorem concrete_l2_graph_pair_energy_prefix_add_le_prefix_bound
    (N : ℕ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairAdd p q) ≤
      (2 : ℝ) • concreteL2GraphPairEnergyPrefix N p +
        (2 : ℝ) • concreteL2GraphPairEnergyPrefix N q := by
  calc
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairAdd p q)
        ≤ (Finset.range N).sum (fun n =>
            ((2 : ℝ) • concreteL2GraphPairEnergyTerm p n +
              (2 : ℝ) • concreteL2GraphPairEnergyTerm q n)) :=
      concrete_l2_graph_pair_energy_prefix_add_le_sum_bound N p q
    _ = (Finset.range N).sum (fun n => (2 : ℝ) • concreteL2GraphPairEnergyTerm p n) +
          (Finset.range N).sum (fun n => (2 : ℝ) • concreteL2GraphPairEnergyTerm q n) := by
      rw [Finset.sum_add_distrib]
    _ = (2 : ℝ) • (Finset.range N).sum (fun n => concreteL2GraphPairEnergyTerm p n) +
          (2 : ℝ) • (Finset.range N).sum (fun n => concreteL2GraphPairEnergyTerm q n) := by
      rw [← Finset.smul_sum, ← Finset.smul_sum]
    _ = (2 : ℝ) • concreteL2GraphPairEnergyPrefix N p +
          (2 : ℝ) • concreteL2GraphPairEnergyPrefix N q := by
      rfl

/-- R2q readiness: the finite prefix additive bound is available. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneSurfaceReady ∧
  (∀ (N : ℕ) (p q : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairAdd p q) ≤
      (2 : ℝ) • concreteL2GraphPairEnergyPrefix N p +
        (2 : ℝ) • concreteL2GraphPairEnergyPrefix N q)

/-- Readiness theorem for R2q. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_add_bound_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBoundSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_general_monotone_surface_ready
    concrete_l2_graph_pair_energy_prefix_add_le_prefix_bound

/-- Boundary marker for R2q. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBoundHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBoundSurfaceReady

/-- Boundary theorem for R2q. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_add_bound_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBoundHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_add_bound_surface_ready

end

end MathlibAnalytic
end MGAP4D
