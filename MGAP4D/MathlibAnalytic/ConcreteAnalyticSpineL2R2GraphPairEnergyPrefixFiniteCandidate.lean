import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- A bounded, nonnegative finite-energy candidate generated from finite-prefix
quadratic envelopes.  This is a bookkeeping predicate: it records that the
`sSup` candidate is finite relative to an explicit bound.  It is not a limit
identification, not a graph-norm completion, and not an operator-domain claim. -/
def concreteL2GraphPairEnergyPrefixFiniteCandidate
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) : Prop :=
  ∃ B : ℝ,
    0 ≤ concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q ∧
      concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q ≤ B

/-- Under component prefix bounds, the `sSup` quadratic-envelope candidate is
nonnegative. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_nonneg
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    0 ≤ concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q := by
  exact le_trans
    (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_nonneg 0 a b p q)
    (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_supCandidate
      a b p q Bp Bq hp hq 0)

/-- Under component prefix bounds, the finite-prefix quadratic-envelope `sSup`
candidate is a finite-energy candidate. -/
theorem concrete_l2_graph_pair_energy_prefix_finite_candidate_of_component_bounds
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    concreteL2GraphPairEnergyPrefixFiniteCandidate a b p q := by
  refine ⟨concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq, ?_, ?_⟩
  · exact concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_nonneg
      a b p q Bp Bq hp hq
  · exact concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_le_componentBound
      a b p q Bp Bq hp hq

/-- R2y readiness: the finite-prefix quadratic-envelope supremum has a bounded
nonnegative candidate surface.  This remains below the completed-domain boundary. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidateSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidateSurfaceReady ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    0 ≤ concreteL2GraphPairEnergyPrefixQuadraticEnvelopeSupCandidate a b p q) ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    concreteL2GraphPairEnergyPrefixFiniteCandidate a b p q)

/-- Readiness theorem for R2y. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_finite_candidate_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidateSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_surface_ready <|
      And.intro
        (fun a b p q Bp Bq hp hq =>
          concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_nonneg
            a b p q Bp Bq hp hq)
        (fun a b p q Bp Bq hp hq =>
          concrete_l2_graph_pair_energy_prefix_finite_candidate_of_component_bounds
            a b p q Bp Bq hp hq)

/-- Boundary marker for R2y. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidateSurfaceReady

/-- Boundary theorem for R2y. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_finite_candidate_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_finite_candidate_surface_ready

end

end MathlibAnalytic
end MGAP4D
