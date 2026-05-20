import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Finite-prefix scalar energy law expressed directly in prefix form.
This is the finite prefix version of the pointwise scalar law, obtained by
moving scalar multiplication through a finite sum with `Finset.smul_sum`. -/
theorem concrete_l2_graph_pair_energy_prefix_smul_eq_prefix_smul
    (N : ℕ) (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul c p) =
      (c ^ 2) • concreteL2GraphPairEnergyPrefix N p := by
  calc
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul c p)
        = (Finset.range N).sum (fun n =>
            (c ^ 2) • concreteL2GraphPairEnergyTerm p n) :=
      concrete_l2_graph_pair_energy_prefix_smul_eq_sum N c p
    _ = (c ^ 2) • (Finset.range N).sum (fun n => concreteL2GraphPairEnergyTerm p n) := by
      rw [← Finset.smul_sum]
    _ = (c ^ 2) • concreteL2GraphPairEnergyPrefix N p := by
      rfl

/-- R2r readiness: finite prefix scalar law is available. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLawSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixAddBoundSurfaceReady ∧
  (∀ (N : ℕ) (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N (concreteL2GraphPairSmul c p) =
      (c ^ 2) • concreteL2GraphPairEnergyPrefix N p)

/-- Readiness theorem for R2r. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_scalar_law_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLawSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_add_bound_surface_ready
    concrete_l2_graph_pair_energy_prefix_smul_eq_prefix_smul

/-- Boundary marker for R2r. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLawHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLawSurfaceReady

/-- Boundary theorem for R2r. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_scalar_law_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixScalarLawHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_scalar_law_surface_ready

end

end MathlibAnalytic
end MGAP4D
