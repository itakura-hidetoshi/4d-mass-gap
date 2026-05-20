import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLaw

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite-prefix energy estimate for a two-term concrete graph-pair linear
combination.  This combines the finite-prefix additive bound with the
finite-prefix scalar law; it remains a finite square-energy estimate, not a
completed graph-norm triangle inequality. -/
theorem concrete_l2_graph_pair_energy_prefix_linear_combination_le
    (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      (2 : ℝ) • ((a ^ 2) • concreteL2GraphPairEnergyPrefix N p) +
        (2 : ℝ) • ((b ^ 2) • concreteL2GraphPairEnergyPrefix N q) := by
  calc
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q))
        ≤ (2 : ℝ) • concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul a p) +
            (2 : ℝ) • concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul b q) :=
      concrete_l2_graph_pair_energy_prefix_add_le_prefix_bound N
        (concreteL2GraphPairSmul a p)
        (concreteL2GraphPairSmul b q)
    _ = (2 : ℝ) • ((a ^ 2) • concreteL2GraphPairEnergyPrefix N p) +
          (2 : ℝ) • ((b ^ 2) • concreteL2GraphPairEnergyPrefix N q) := by
      rw [concrete_l2_graph_pair_energy_prefix_smul_eq_prefix_smul,
        concrete_l2_graph_pair_energy_prefix_smul_eq_prefix_smul]

/-- R2s readiness: finite prefix two-term linear-combination bound is available. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLawSurfaceReady ∧
  (∀ (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      (2 : ℝ) • ((a ^ 2) • concreteL2GraphPairEnergyPrefix N p) +
        (2 : ℝ) • ((b ^ 2) • concreteL2GraphPairEnergyPrefix N q))

/-- Readiness theorem for R2s. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_scalar_law_surface_ready
    concrete_l2_graph_pair_energy_prefix_linear_combination_le

/-- Boundary marker for R2s. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationSurfaceReady

/-- Boundary theorem for R2s. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_surface_ready

end

end MathlibAnalytic
end MGAP4D
