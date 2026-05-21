import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacket

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Prefix-energy boundedness for concrete graph pairs.  This is a deliberately
thin carrier predicate: it only records the existence of a real uniform bound
for all finite energy prefixes.  It is not a convergence statement and not a
completed graph-norm/domain assertion. -/
def concreteL2GraphPairPrefixEnergyBounded
    (p : ConcreteL2GraphPairSpace) : Prop :=
  ∃ B : ℝ, ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ B

/-- The set of concrete graph pairs with uniformly bounded finite energy
prefixes. -/
def concreteL2GraphPairPrefixEnergyBoundedCarrier : Set ConcreteL2GraphPairSpace :=
  { p | concreteL2GraphPairPrefixEnergyBounded p }

/-- Membership in the bounded-prefix carrier is exactly prefix-energy
boundedness. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_carrier_mem_iff
    (p : ConcreteL2GraphPairSpace) :
    p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier ↔
      concreteL2GraphPairPrefixEnergyBounded p := by
  rfl

/-- The zero graph pair belongs to the bounded-prefix carrier. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_zero_mem :
    concreteL2GraphPairZero ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier := by
  refine ⟨0, ?_⟩
  intro N
  rw [concrete_l2_graph_pair_energy_prefix_zero]

/-- The explicit two-term concrete graph-pair linear combination preserves the
bounded-prefix carrier.  The proof uses the quadratic envelope component bound
established in the finite-packet layer. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_linear_combination_mem
    (a b : ℝ) {p q : ConcreteL2GraphPairSpace}
    (hp : p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier)
    (hq : q ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier) :
    concreteL2GraphPairAdd
        (concreteL2GraphPairSmul a p)
        (concreteL2GraphPairSmul b q) ∈
      concreteL2GraphPairPrefixEnergyBoundedCarrier := by
  rcases hp with ⟨Bp, hpB⟩
  rcases hq with ⟨Bq, hqB⟩
  refine ⟨concreteL2GraphPairEnergyPrefixQuadraticEnvelopeComponentBound a b Bp Bq, ?_⟩
  intro N
  exact concrete_l2_graph_pair_energy_prefix_linear_combination_le_componentBound
    a b p q Bp Bq hpB hqB N

/-- The bounded-prefix carrier yields a finite packet for every explicit two-term
linear combination of two carrier elements. -/
theorem concrete_l2_graph_pair_prefix_energy_bounded_linear_combination_finite_packet
    (a b : ℝ) {p q : ConcreteL2GraphPairSpace}
    (hp : p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier)
    (hq : q ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier) :
    concreteL2GraphPairEnergyPrefixLinearCombinationFinitePacket a b p q := by
  rcases hp with ⟨Bp, hpB⟩
  rcases hq with ⟨Bq, hqB⟩
  exact concrete_l2_graph_pair_energy_prefix_linear_combination_finite_packet_of_component_bounds
    a b p q Bp Bq hpB hqB

/-- R2aa readiness: bounded-prefix graph pairs form a zero-containing carrier
stable under the explicit two-term concrete graph-pair linear-combination
operation.  This is still a prefix-energy carrier surface, not a graph-norm
subspace theorem. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrierSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationFinitePacketSurfaceReady ∧
  concreteL2GraphPairZero ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier ∧
  (∀ (a b : ℝ) {p q : ConcreteL2GraphPairSpace},
    p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    q ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    concreteL2GraphPairAdd
        (concreteL2GraphPairSmul a p)
        (concreteL2GraphPairSmul b q) ∈
      concreteL2GraphPairPrefixEnergyBoundedCarrier) ∧
  (∀ (a b : ℝ) {p q : ConcreteL2GraphPairSpace},
    p ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    q ∈ concreteL2GraphPairPrefixEnergyBoundedCarrier →
    concreteL2GraphPairEnergyPrefixLinearCombinationFinitePacket a b p q)

/-- Readiness theorem for R2aa. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_carrier_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrierSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_finite_packet_surface_ready <|
      And.intro
        concrete_l2_graph_pair_prefix_energy_bounded_zero_mem <|
          And.intro
            (fun a b p q hp hq =>
              concrete_l2_graph_pair_prefix_energy_bounded_linear_combination_mem
                a b hp hq)
            (fun a b p q hp hq =>
              concrete_l2_graph_pair_prefix_energy_bounded_linear_combination_finite_packet
                a b hp hq)

/-- Boundary marker for R2aa. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrierHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrierSurfaceReady

/-- Boundary theorem for R2aa. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_carrier_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedCarrierHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_bounded_carrier_surface_ready

end

end MathlibAnalytic
end MGAP4D
