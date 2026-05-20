import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidate

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- A finite-energy packet for the concrete two-term graph-pair linear combination.
It records both the bounded `sSup` envelope candidate and a uniform finite-prefix
energy bound for the actual linear combination.  This remains a prefix-level
boundedness statement, not a completed graph-norm or closed-operator assertion. -/
def concreteL2GraphPairEnergyPrefixLinearCombinationFinitePacket
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) : Prop :=
  ∃ B : ℝ,
    concreteL2GraphPairEnergyPrefixFiniteCandidate a b p q ∧
      ∀ N : ℕ,
        concreteL2GraphPairEnergyPrefix N
          (concreteL2GraphPairAdd
            (concreteL2GraphPairSmul a p)
            (concreteL2GraphPairSmul b q)) ≤ B

/-- Under component prefix bounds, every finite prefix of the concrete two-term
linear combination is bounded by the same explicit quadratic component envelope
that bounds the `sSup` candidate. -/
theorem concrete_l2_graph_pair_energy_prefix_linear_combination_le_componentBound
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq)
    (N : ℕ) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq := by
  exact le_trans
    (concrete_l2_graph_pair_energy_prefix_linear_combination_le_quadratic_envelope
      N a b p q)
    (le_trans
      (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_supCandidate
        a b p q Bp Bq hp hq N)
      (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_supCandidate_le_componentBound
        a b p q Bp Bq hp hq))

/-- Component prefix bounds generate a finite-energy packet for the concrete
two-term graph-pair linear combination. -/
theorem concrete_l2_graph_pair_energy_prefix_linear_combination_finite_packet_of_component_bounds
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    concreteL2GraphPairEnergyPrefixLinearCombinationFinitePacket a b p q := by
  refine ⟨concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq, ?_, ?_⟩
  · exact concrete_l2_graph_pair_energy_prefix_finite_candidate_of_component_bounds
      a b p q Bp Bq hp hq
  · intro N
    exact concrete_l2_graph_pair_energy_prefix_linear_combination_le_componentBound
      a b p q Bp Bq hp hq N

/-- R2z readiness: component-bounded inputs give a finite-energy packet for the
actual concrete graph-pair linear combination, while preserving the prefix-only
boundary. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacketSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixFiniteCandidateSurfaceReady ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    ∀ N : ℕ,
      concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
        concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq) ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    concreteL2GraphPairEnergyPrefixLinearCombinationFinitePacket a b p q)

/-- Readiness theorem for R2z. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_finite_packet_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacketSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_finite_candidate_surface_ready <|
      And.intro
        (fun a b p q Bp Bq hp hq N =>
          concrete_l2_graph_pair_energy_prefix_linear_combination_le_componentBound
            a b p q Bp Bq hp hq N)
        (fun a b p q Bp Bq hp hq =>
          concrete_l2_graph_pair_energy_prefix_linear_combination_finite_packet_of_component_bounds
            a b p q Bp Bq hp hq)

/-- Boundary marker for R2z. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacketHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacketSurfaceReady

/-- Boundary theorem for R2z. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_finite_packet_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacketHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_finite_packet_surface_ready

end

end MathlibAnalytic
end MGAP4D
