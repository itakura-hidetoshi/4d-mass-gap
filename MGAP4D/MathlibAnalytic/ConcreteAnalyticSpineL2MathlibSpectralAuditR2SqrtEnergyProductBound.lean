import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyUniform

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Pointwise product bound for square-root energy terms.

This is the elementary estimate needed before the infinite summed Cauchy step:
`sqrt(e_p n) * sqrt(e_q n) ≤ (e_p n + e_q n) / 2`.
It gives a summable majorant built from the already summable energy terms.
-/
theorem concrete_l2_sqrt_energy_product_le_half_sum
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) ≤
      (concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n) / (2 : ℝ) := by
  let a := concreteL2GraphPairEnergyTerm p n
  let b := concreteL2GraphPairEnergyTerm q n
  have ha : 0 ≤ a := by
    dsimp [a]
    exact concrete_l2_graph_pair_energy_term_nonneg p n
  have hb : 0 ≤ b := by
    dsimp [b]
    exact concrete_l2_graph_pair_energy_term_nonneg q n
  have htwo := concrete_l2_two_mul_le_sq_add_sq (Real.sqrt a) (Real.sqrt b)
  have hsq_a : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt ha
  have hsq_b : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb
  have htwice :
      (2 : ℝ) * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
    nlinarith
  nlinarith

/-- Package: pointwise product bound for square-root energy terms. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumBound : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) ≤
      (concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n) / (2 : ℝ)

/-- The pointwise square-root energy product bound package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_bound :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumBound := by
  intro p q n
  exact concrete_l2_sqrt_energy_product_le_half_sum p q n

/--
Surface for the pointwise square-root energy product bound.
-/
structure ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurface where
  finitePrefixUniformReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurfaceReady
  productBound : concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumBound
  boundaryNotProductSummability : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete pointwise product-bound surface. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurface :
    ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurface :=
  { finitePrefixUniformReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_uniform_surface_ready
    productBound :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_bound
    boundaryNotProductSummability := True
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the pointwise product-bound surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2FinitePrefixCauchyUniformSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumBound

/-- Readiness theorem for the pointwise product-bound surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_bound_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_finite_prefix_cauchy_uniform_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_bound⟩

end

end MathlibAnalytic
end MGAP4D
