import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBounded

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The coefficient-weighted component bound used for the finite-prefix
quadratic envelope. -/
def concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound
    (a b Bp Bq : ℝ) : ℝ :=
  (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq)

/-- Uniform component bounds make the range of finite-prefix quadratic envelopes
bounded above.  This is only a bounded-range API, not a supremum or convergence
construction. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    BddAbove (Set.range fun N : ℕ =>
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q) := by
  refine ⟨concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq, ?_⟩
  intro x hx
  rcases hx with ⟨N, rfl⟩
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound
  exact concrete_l2_graph_pair_energy_prefix_quadratic_envelope_uniform_bound
    a b p q Bp Bq hp hq N

/-- R2w readiness: finite-prefix quadratic envelopes have a `BddAbove` range API
under uniform component bounds. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRangeSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBoundedSurfaceReady ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    BddAbove (Set.range fun N : ℕ =>
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q))

/-- Readiness theorem for R2w. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRangeSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bounded_surface_ready
    (fun a b p q Bp Bq hp hq =>
      concrete_l2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range a b p q Bp Bq hp hq)

/-- Boundary marker for R2w. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRangeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRangeSurfaceReady

/-- Boundary theorem for R2w. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRangeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range_surface_ready

end

end MathlibAnalytic
end MGAP4D
