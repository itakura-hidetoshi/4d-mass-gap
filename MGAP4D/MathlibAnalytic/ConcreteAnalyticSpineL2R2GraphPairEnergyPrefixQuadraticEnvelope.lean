import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombination

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- The finite-prefix quadratic envelope controlling a two-term concrete graph-pair
linear combination.  This is still a finite square-energy envelope, not a
completed graph norm. -/
def concreteL2GraphPairEnergyPrefixQuadraticEnvelope
    (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) : ℝ :=
  (2 : ℝ) • ((a ^ 2) • concreteL2GraphPairEnergyPrefix N p) +
    (2 : ℝ) • ((b ^ 2) • concreteL2GraphPairEnergyPrefix N q)

/-- The finite-prefix quadratic envelope is nonnegative.  The proof deliberately
uses mathlib's square and product nonnegativity lemmas before reducing scalar
multiplication on `ℝ` to multiplication. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_nonneg
    (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) :
    0 ≤ concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q := by
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelope
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hp : 0 ≤ concreteL2GraphPairEnergyPrefix N p :=
    concrete_l2_graph_pair_energy_prefix_nonneg N p
  have hq : 0 ≤ concreteL2GraphPairEnergyPrefix N q :=
    concrete_l2_graph_pair_energy_prefix_nonneg N q
  have hleft : 0 ≤ (2 : ℝ) * ((a ^ 2) * concreteL2GraphPairEnergyPrefix N p) :=
    mul_nonneg htwo (mul_nonneg ha2 hp)
  have hright : 0 ≤ (2 : ℝ) * ((b ^ 2) * concreteL2GraphPairEnergyPrefix N q) :=
    mul_nonneg htwo (mul_nonneg hb2 hq)
  simpa [smul_eq_mul] using add_nonneg hleft hright

/-- The two-term finite-prefix energy is controlled by its quadratic envelope. -/
theorem concrete_l2_graph_pair_energy_prefix_linear_combination_le_quadratic_envelope
    (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q := by
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelope
  exact concrete_l2_graph_pair_energy_prefix_linear_combination_le N a b p q

/-- R2t readiness: finite-prefix quadratic envelope is available and nonnegative. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixLinearCombinationSurfaceReady ∧
  (∀ (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace),
    0 ≤ concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q) ∧
  (∀ (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q)

/-- Readiness theorem for R2t. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_linear_combination_surface_ready <|
      And.intro
        concrete_l2_graph_pair_energy_prefix_quadratic_envelope_nonneg
        concrete_l2_graph_pair_energy_prefix_linear_combination_le_quadratic_envelope

/-- Boundary marker for R2t. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSurfaceReady

/-- Boundary theorem for R2t. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_surface_ready

end

end MathlibAnalytic
end MGAP4D
