import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRange

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The supremal candidate attached to the finite-prefix quadratic envelope.
This is only the `sSup` of the prefix range.  It is not yet a convergence
claim, a completed graph norm, or an operator-domain statement. -/
def concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) : ℝ :=
  sSup (Set.range fun N : ℕ =>
    concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q)

/-- Under uniform component prefix bounds, every finite-prefix quadratic envelope
lies below its `sSup` candidate. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_supCandidate
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq)
    (N : ℕ) :
    concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q := by
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate
  exact le_csSup
    (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range
      a b p q Bp Bq hp hq)
    ⟨N, rfl⟩

/-- The finite-prefix quadratic-envelope `sSup` candidate remains below the
same explicit component-bound envelope whenever uniform component bounds are
available. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_le_componentBound
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq := by
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate
  refine csSup_le ?hne ?hub
  · exact ⟨concreteL2GraphPairEnergyPrefixQuadraticEnvelope 0 a b p q, ⟨0, rfl⟩⟩
  · intro x hx
    rcases hx with ⟨N, rfl⟩
    unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound
    exact concrete_l2_graph_pair_energy_prefix_quadratic_envelope_uniform_bound
      a b p q Bp Bq hp hq N

/-- R2x readiness: the bounded finite-prefix quadratic envelope now has a
mathlib `sSup` candidate API, while preserving the non-convergence boundary. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidateSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBddAboveRangeSurfaceReady ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    ∀ N : ℕ,
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
        concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q) ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq)

/-- Readiness theorem for R2x. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidateSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bddAbove_range_surface_ready <|
      And.intro
        (fun a b p q Bp Bq hp hq N =>
          concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_supCandidate
            a b p q Bp Bq hp hq N)
        (fun a b p q Bp Bq hp hq =>
          concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_le_componentBound
            a b p q Bp Bq hp hq)

/-- Boundary marker for R2x. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidateSurfaceReady

/-- Boundary theorem for R2x. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_surface_ready

end

end MathlibAnalytic
end MGAP4D
