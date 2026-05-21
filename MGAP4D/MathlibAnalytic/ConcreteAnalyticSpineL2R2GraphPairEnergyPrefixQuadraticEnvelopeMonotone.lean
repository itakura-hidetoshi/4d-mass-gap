import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelope

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- Monotonicity of the finite-prefix quadratic envelope.  The proof lifts the
existing finite-prefix monotonicity through the nonnegative square coefficients
and the nonnegative outer factor `2`.  This is still finite-prefix control only;
no supremum, limit, or completed graph norm is asserted. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_le
    {N M : ℕ} (hNM : N ≤ M) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope M a b p q := by
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelope
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hpNM : concreteL2GraphPairEnergyPrefix N p ≤ concreteL2GraphPairEnergyPrefix M p :=
    concrete_l2_graph_pair_energy_prefix_le_of_le hNM p
  have hqNM : concreteL2GraphPairEnergyPrefix N q ≤ concreteL2GraphPairEnergyPrefix M q :=
    concrete_l2_graph_pair_energy_prefix_le_of_le hNM q
  have hpScale :
      (a ^ 2) * concreteL2GraphPairEnergyPrefix N p ≤
        (a ^ 2) * concreteL2GraphPairEnergyPrefix M p :=
    mul_le_mul_of_nonneg_left hpNM ha2
  have hqScale :
      (b ^ 2) * concreteL2GraphPairEnergyPrefix N q ≤
        (b ^ 2) * concreteL2GraphPairEnergyPrefix M q :=
    mul_le_mul_of_nonneg_left hqNM hb2
  have hpOuter :
      (2 : ℝ) * ((a ^ 2) * concreteL2GraphPairEnergyPrefix N p) ≤
        (2 : ℝ) * ((a ^ 2) * concreteL2GraphPairEnergyPrefix M p) :=
    mul_le_mul_of_nonneg_left hpScale htwo
  have hqOuter :
      (2 : ℝ) * ((b ^ 2) * concreteL2GraphPairEnergyPrefix N q) ≤
        (2 : ℝ) * ((b ^ 2) * concreteL2GraphPairEnergyPrefix M q) :=
    mul_le_mul_of_nonneg_left hqScale htwo
  simpa [smul_eq_mul] using add_le_add hpOuter hqOuter

/-- A finite-prefix two-term linear combination at level `N` is controlled by
the quadratic envelope at any later prefix `M`. -/
theorem concrete_l2_graph_pair_energy_prefix_linear_combination_le_later_quadratic_envelope
    {N M : ℕ} (hNM : N ≤ M) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope M a b p q := by
  exact le_trans
    (concrete_l2_graph_pair_energy_prefix_linear_combination_le_quadratic_envelope N a b p q)
    (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_le hNM a b p q)

/-- R2u readiness: quadratic envelope monotonicity and later-prefix control are
available. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotoneSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeSurfaceReady ∧
  (∀ {N M : ℕ}, N ≤ M → ∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope M a b p q) ∧
  (∀ {N M : ℕ}, N ≤ M → ∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace),
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope M a b p q)

/-- Readiness theorem for R2u. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_monotone_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotoneSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_surface_ready <|
      And.intro
        (fun hNM a b p q =>
          concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_le hNM a b p q)
        (fun hNM a b p q =>
          concrete_l2_graph_pair_energy_prefix_linear_combination_le_later_quadratic_envelope hNM a b p q)

/-- Boundary marker for R2u. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotoneHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotoneSurfaceReady

/-- Boundary theorem for R2u. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_monotone_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotoneHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_monotone_surface_ready

end

end MathlibAnalytic
end MGAP4D
