import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Nonnegativity of the square-root energy product series term.
-/
theorem concrete_l2_sqrt_energy_product_nonneg
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    0 ≤ Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) := by
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/--
Nonnegativity of the half-sum majorant term.
-/
theorem concrete_l2_sqrt_energy_product_half_sum_nonneg
    (p q : ConcreteL2GraphPairSpace) (n : ℕ) :
    0 ≤ (concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n) / (2 : ℝ) := by
  have hp : 0 ≤ concreteL2GraphPairEnergyTerm p n :=
    concrete_l2_graph_pair_energy_term_nonneg p n
  have hq : 0 ≤ concreteL2GraphPairEnergyTerm q n :=
    concrete_l2_graph_pair_energy_term_nonneg q n
  nlinarith

/--
Comparison frontier for square-root energy product summability.

The product term is nonnegative and bounded above by a summable nonnegative
majorant.  The next step is to apply the appropriate mathlib comparison lemma
for `Summable`.
-/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurfaceReady

/-- Readiness theorem for the product comparison frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_comparison_frontier_ready :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summability_frontier_surface_ready

/-- Package: nonnegativity of the product term. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductNonneg : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    0 ≤ Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)

/-- The product-term nonnegativity package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_nonneg :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductNonneg := by
  intro p q n
  exact concrete_l2_sqrt_energy_product_nonneg p q n

/-- Package: nonnegativity of the half-sum majorant. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumNonneg : Prop :=
  ∀ (p q : ConcreteL2GraphPairSpace) (n : ℕ),
    0 ≤ (concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n) / (2 : ℝ)

/-- The half-sum majorant nonnegativity package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_nonneg :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumNonneg := by
  intro p q n
  exact concrete_l2_sqrt_energy_product_half_sum_nonneg p q n

/--
Surface collecting the comparison data for product summability.
-/
structure ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurface where
  summabilityFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurfaceReady
  productNonneg : concreteL2MathlibSpectralAuditR2SqrtEnergyProductNonneg
  halfSumNonneg : concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumNonneg
  productBound : concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumBound
  halfSumSummable : concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumSummable
  productSummableTarget : Prop
  boundaryNotProductSummable : Prop
  boundaryNotSummedCauchy : Prop

/-- Concrete comparison frontier surface. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurface :=
  { summabilityFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summability_frontier_surface_ready
    productNonneg :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_nonneg
    halfSumNonneg :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_nonneg
    productBound :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_bound
    halfSumSummable :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_summable
    productSummableTarget :=
      concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummableTarget
    boundaryNotProductSummable := True
    boundaryNotSummedCauchy := True }

/-- Readiness predicate for product comparison frontier surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontier ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductNonneg ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumNonneg ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumBound ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumSummable

/-- Readiness theorem for product comparison frontier surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_comparison_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_comparison_frontier_ready,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_nonneg,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_nonneg,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_bound,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_summable⟩

end

end MathlibAnalytic
end MGAP4D
