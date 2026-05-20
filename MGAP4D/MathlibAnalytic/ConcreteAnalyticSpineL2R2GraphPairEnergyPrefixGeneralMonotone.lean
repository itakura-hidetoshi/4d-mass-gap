import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixStep

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- General finite-prefix monotonicity for the concrete graph-pair energy prefix.
This proof uses the mathlib finite-sum lemma `Finset.sum_le_sum_of_subset_of_nonneg`:
the earlier range is a subset of the later range, and the newly added energy
terms are nonnegative.  This is still only a finite-prefix result, not a limit
or graph-norm convergence theorem. -/
theorem concrete_l2_graph_pair_energy_prefix_le_of_le
    {N M : ℕ} (hNM : N ≤ M) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N p ≤ concreteL2GraphPairEnergyPrefix M p := by
  unfold concreteL2GraphPairEnergyPrefix
  have hsubset : Finset.range N ⊆ Finset.range M := by
    intro n hn
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hn) hNM)
  have hnonneg : ∀ n ∈ Finset.range M, n ∉ Finset.range N →
      0 ≤ concreteL2GraphPairEnergyTerm p n := by
    intro n _hnM _hnN
    exact concrete_l2_graph_pair_energy_term_nonneg p n
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset hnonneg

/-- R2p finite graph-pair energy prefix general monotonicity surface. -/
structure ConcreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface where
  r2oReady : concreteAnalyticSpineL2R2GraphPairEnergyPrefixStepSurfaceReady
  prefixGeneralMonotone : ∀ {N M : ℕ}, N ≤ M → ∀ (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N p ≤ concreteL2GraphPairEnergyPrefix M p
  prefixSuccStep : ∀ (N : ℕ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N.succ p =
      concreteL2GraphPairEnergyPrefix N p + concreteL2GraphPairEnergyTerm p N
  prefixSuccMonotone : ∀ (N : ℕ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N p ≤ concreteL2GraphPairEnergyPrefix N.succ p
  boundaryNotEnergyLimitConstruction : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormConvergenceTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2p finite graph-pair energy prefix general monotonicity surface. -/
def concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface :
    ConcreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface :=
  { r2oReady := concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_step_surface_ready
    prefixGeneralMonotone := fun hNM p => concrete_l2_graph_pair_energy_prefix_le_of_le hNM p
    prefixSuccStep := concrete_l2_graph_pair_energy_prefix_succ_eq_add_term
    prefixSuccMonotone := concrete_l2_graph_pair_energy_prefix_le_succ
    boundaryNotEnergyLimitConstruction := True
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormConvergenceTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2p readiness. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixStepSurfaceReady ∧
  (∀ {N M : ℕ}, N ≤ M → ∀ (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N p ≤ concreteL2GraphPairEnergyPrefix M p) ∧
  (∀ (N : ℕ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N.succ p =
      concreteL2GraphPairEnergyPrefix N p + concreteL2GraphPairEnergyTerm p N) ∧
  (∀ (N : ℕ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N p ≤ concreteL2GraphPairEnergyPrefix N.succ p) ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotEnergyLimitConstruction ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotGraphNormTopology ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotGraphNormConvergenceTheorem ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphPairEnergyPrefixGeneralMonotoneSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for R2p. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_general_monotone_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneSurfaceReady
  exact And.intro concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_step_surface_ready <|
    And.intro (fun hNM p => concrete_l2_graph_pair_energy_prefix_le_of_le hNM p) <|
      And.intro concrete_l2_graph_pair_energy_prefix_succ_eq_add_term <|
        And.intro concrete_l2_graph_pair_energy_prefix_le_succ <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial trivial

/-- Boundary marker for R2p. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneSurfaceReady

/-- Boundary theorem for R2p. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_general_monotone_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixGeneralMonotoneHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_general_monotone_surface_ready

end

end MathlibAnalytic
end MGAP4D
