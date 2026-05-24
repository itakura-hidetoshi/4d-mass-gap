import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Summability of the square-root energy product series.

This applies the mathlib comparison theorem `Summable.of_nonneg_of_le` in the
same argument order used in mathlib source:

`Summable.of_nonneg_of_le h_nonneg h_le h_majorant`.
-/
theorem concrete_l2_sqrt_energy_product_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ =>
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) := by
  refine Summable.of_nonneg_of_le
    (fun n : ℕ => concrete_l2_sqrt_energy_product_nonneg p q n)
    (fun n : ℕ => concrete_l2_sqrt_energy_product_le_half_sum p q n)
    (concrete_l2_sqrt_energy_product_half_sum_summable p q)

/-- Package: product summability for square-root energy terms. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummable : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ =>
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)

/-- The product summability package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summable :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummable := by
  intro p q
  exact concrete_l2_sqrt_energy_product_summable p q

/-- Surface for product summability. -/
structure ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurface where
  comparisonFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurfaceReady
  productSummable : concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummable
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete product summability surface. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurface :
    ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurface :=
  { comparisonFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_comparison_frontier_surface_ready
    productSummable :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summable
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for product summability surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductComparisonFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummable

/-- Readiness theorem for product summability surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summable_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_comparison_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summable⟩

end

end MathlibAnalytic
end MGAP4D
