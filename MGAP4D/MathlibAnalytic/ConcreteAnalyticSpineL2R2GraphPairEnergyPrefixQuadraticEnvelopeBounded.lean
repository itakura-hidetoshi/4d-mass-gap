import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotone

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- If both component finite-prefix energies are bounded at a given prefix, then
the quadratic envelope is bounded by the corresponding coefficient-weighted
component bounds.  This is a finite-prefix precontrol lemma; it does not assert
existence of an infinite energy limit. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_component_bounds
    (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
      (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq) := by
  unfold concreteL2GraphPairEnergyPrefixQuadraticEnvelope
  have htwo : (0 : ℝ) ≤ 2 := by norm_num
  have ha2 : 0 ≤ a ^ 2 := sq_nonneg a
  have hb2 : 0 ≤ b ^ 2 := sq_nonneg b
  have hpScale :
      (a ^ 2) * concreteL2GraphPairEnergyPrefix N p ≤ (a ^ 2) * Bp :=
    mul_le_mul_of_nonneg_left hp ha2
  have hqScale :
      (b ^ 2) * concreteL2GraphPairEnergyPrefix N q ≤ (b ^ 2) * Bq :=
    mul_le_mul_of_nonneg_left hq hb2
  have hpOuter :
      (2 : ℝ) * ((a ^ 2) * concreteL2GraphPairEnergyPrefix N p) ≤
        (2 : ℝ) * ((a ^ 2) * Bp) :=
    mul_le_mul_of_nonneg_left hpScale htwo
  have hqOuter :
      (2 : ℝ) * ((b ^ 2) * concreteL2GraphPairEnergyPrefix N q) ≤
        (2 : ℝ) * ((b ^ 2) * Bq) :=
    mul_le_mul_of_nonneg_left hqScale htwo
  simpa [smul_eq_mul] using add_le_add hpOuter hqOuter

/-- Uniform component bounds imply a uniform finite-prefix quadratic-envelope
bound. -/
theorem concrete_l2_graph_pair_energy_prefix_quadratic_envelope_uniform_bound
    (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hp : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp)
    (hq : ∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) :
    ∀ N : ℕ,
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
        (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq) := by
  intro N
  exact concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_component_bounds
    N a b p q Bp Bq (hp N) (hq N)

/-- A finite-prefix two-term linear combination is bounded by a later component
bound envelope whenever its index is no larger than the later controlled index. -/
theorem concrete_l2_graph_pair_energy_prefix_linear_combination_le_later_component_bounds
    {N M : ℕ} (hNM : N ≤ M) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ)
    (hpM : concreteL2GraphPairEnergyPrefix M p ≤ Bp)
    (hqM : concreteL2GraphPairEnergyPrefix M q ≤ Bq) :
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq) := by
  exact le_trans
    (concrete_l2_graph_pair_energy_prefix_linear_combination_le_later_quadratic_envelope
      hNM a b p q)
    (concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_component_bounds
      M a b p q Bp Bq hpM hqM)

/-- R2v readiness: uniform bounded quadratic-envelope precontrol is available. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBoundedSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeMonotoneSurfaceReady ∧
  (∀ (N : ℕ) (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    concreteL2GraphPairEnergyPrefix N p ≤ Bp →
    concreteL2GraphPairEnergyPrefix N q ≤ Bq →
    concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
      (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq)) ∧
  (∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N p ≤ Bp) →
    (∀ N : ℕ, concreteL2GraphPairEnergyPrefix N q ≤ Bq) →
    ∀ N : ℕ,
      concreteL2GraphPairEnergyPrefixQuadraticEnvelope N a b p q ≤
        (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq)) ∧
  (∀ {N M : ℕ}, N ≤ M → ∀ (a b : ℝ) (p q : ConcreteL2GraphPairSpace) (Bp Bq : ℝ),
    concreteL2GraphPairEnergyPrefix M p ≤ Bp →
    concreteL2GraphPairEnergyPrefix M q ≤ Bq →
    concreteL2GraphPairEnergyPrefix N
        (concreteL2GraphPairAdd
          (concreteL2GraphPairSmul a p)
          (concreteL2GraphPairSmul b q)) ≤
      (2 : ℝ) • ((a ^ 2) • Bp) + (2 : ℝ) • ((b ^ 2) • Bq))

/-- Readiness theorem for R2v. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bounded_surface_ready :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBoundedSurfaceReady := by
  exact And.intro
    concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_monotone_surface_ready <|
      And.intro
        concrete_l2_graph_pair_energy_prefix_quadratic_envelope_le_of_component_bounds <|
          And.intro
            concrete_l2_graph_pair_energy_prefix_quadratic_envelope_uniform_bound
            (fun hNM a b p q Bp Bq hpM hqM =>
              concrete_l2_graph_pair_energy_prefix_linear_combination_le_later_component_bounds
                hNM a b p q Bp Bq hpM hqM)

/-- Boundary marker for R2v. -/
def concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBoundedHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBoundedSurfaceReady

/-- Boundary theorem for R2v. -/
theorem concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bounded_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphPairEnergyPrefixQuadraticEnvelopeBoundedHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_pair_energy_prefix_quadratic_envelope_bounded_surface_ready

end

end MathlibAnalytic
end MGAP4D
