import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergy

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Completed graph energy is nonnegative.

This is the first genuine inequality theorem after introducing the completed
`tsum` energy functional.  It uses the pointwise nonnegativity of the graph-pair
square-energy terms.
-/
theorem concrete_l2_completed_graph_energy_nonneg
    (p : ConcreteL2GraphPairSpace) :
    0 ≤ concreteL2CompletedGraphEnergy p := by
  unfold concreteL2CompletedGraphEnergy
  exact tsum_nonneg fun n =>
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_nonneg p n

/-- Completed graph-energy nonnegativity package. -/
def concreteL2MathlibSpectralAuditR2CompletedGraphEnergyNonneg : Prop :=
  ∀ p : ConcreteL2GraphPairSpace, 0 ≤ concreteL2CompletedGraphEnergy p

/-- Completed graph-energy nonnegativity is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_nonneg :
    concreteL2MathlibSpectralAuditR2CompletedGraphEnergyNonneg := by
  exact concrete_l2_completed_graph_energy_nonneg

/--
Completed graph-energy surface with nonnegativity included.
-/
structure ConcreteL2MathlibSpectralAuditR2CompletedGraphEnergyNonnegSurface where
  completedEnergyReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySurfaceReady
  completedEnergy : ConcreteL2GraphPairSpace → ℝ
  completedEnergy_eq_tsum : ∀ p : ConcreteL2GraphPairSpace,
    completedEnergy p = ∑' n : ℕ, concreteL2GraphPairEnergyTerm p n
  nonneg : ∀ p : ConcreteL2GraphPairSpace, 0 ≤ completedEnergy p
  zeroEnergy : completedEnergy concreteL2GraphPairZero = 0
  boundaryNotGraphNorm : Prop
  boundaryNotGraphNormTopology : Prop
  boundaryNotGraphNormDensity : Prop

/-- Concrete completed graph-energy nonnegativity surface. -/
def concreteL2MathlibSpectralAuditR2CompletedGraphEnergyNonnegSurface :
    ConcreteL2MathlibSpectralAuditR2CompletedGraphEnergyNonnegSurface :=
  { completedEnergyReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_surface_ready
    completedEnergy := concreteL2CompletedGraphEnergy
    completedEnergy_eq_tsum := concrete_l2_completed_graph_energy_eq_tsum
    nonneg := concrete_l2_completed_graph_energy_nonneg
    zeroEnergy := concrete_l2_completed_graph_energy_zero
    boundaryNotGraphNorm := True
    boundaryNotGraphNormTopology := True
    boundaryNotGraphNormDensity := True }

/-- Readiness predicate for the completed graph-energy nonnegativity surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyNonnegSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CompletedGraphEnergyNonneg ∧
  concreteL2MathlibSpectralAuditR2CompletedGraphEnergyZeroLaw ∧
  concreteL2MathlibSpectralAuditR2GraphEnergyCompletionFrontierBoundaryHeld

/-- Readiness theorem for the completed graph-energy nonnegativity surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_nonneg_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyNonnegSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyNonnegSurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_nonneg,
    concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_zero_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_completion_frontier_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
