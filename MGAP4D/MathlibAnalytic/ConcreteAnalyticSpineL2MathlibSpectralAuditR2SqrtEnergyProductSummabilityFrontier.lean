import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Summability frontier for the square-root energy product series.

The pointwise majorant
`sqrt(e_p n) * sqrt(e_q n) ≤ (e_p n + e_q n)/2`
reduces product summability to the already-established summability of graph
energy terms.  This file first packages the summable half-sum majorant using
only the infinite-sum API already used successfully in this PR stack.
-/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontier : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurfaceReady

/-- Readiness theorem for the product summability frontier. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summability_frontier_ready :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontier := by
  exact concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_bound_surface_ready

/--
The half-sum majorant for the square-root energy product is summable.
-/
theorem concrete_l2_sqrt_energy_product_half_sum_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ =>
      (concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n) / (2 : ℝ) := by
  have hp : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm p n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable p
  have hq : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm q n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable q
  have hsum : Summable fun n : ℕ =>
      concreteL2GraphPairEnergyTerm p n + concreteL2GraphPairEnergyTerm q n :=
    hp.add hq
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    hsum.mul_left ((2 : ℝ)⁻¹)

/-- Package: summability of the half-sum product majorant. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumSummable : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ =>
      (concreteL2GraphPairEnergyTerm p n +
        concreteL2GraphPairEnergyTerm q n) / (2 : ℝ)

/-- The half-sum majorant summability package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_summable :
    concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumSummable := by
  intro p q
  exact concrete_l2_sqrt_energy_product_half_sum_summable p q

/--
Target: summability of the square-root energy product series.
-/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummableTarget : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ =>
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)

/--
Surface for the product summability frontier.
-/
structure ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurface where
  productBoundReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductBoundSurfaceReady
  halfSumSummable : concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumSummable
  productSummableTarget : Prop
  boundaryNotProductSummability : Prop
  boundaryNotSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete product summability frontier surface. -/
def concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurface :
    ConcreteL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurface :=
  { productBoundReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_bound_surface_ready
    halfSumSummable :=
      concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_summable
    productSummableTarget :=
      concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummableTarget
    boundaryNotProductSummability := True
    boundaryNotSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for the product summability frontier surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontier ∧
  concreteL2MathlibSpectralAuditR2SqrtEnergyProductHalfSumSummable

/-- Readiness theorem for the product summability frontier surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summability_frontier_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummabilityFrontierSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summability_frontier_ready,
    concrete_l2_mathlib_spectral_audit_r2_sqrt_energy_product_half_sum_summable⟩

end

end MathlibAnalytic
end MGAP4D
