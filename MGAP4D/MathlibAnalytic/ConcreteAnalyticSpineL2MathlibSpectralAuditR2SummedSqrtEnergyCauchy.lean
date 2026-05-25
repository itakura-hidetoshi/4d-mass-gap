import Mathlib.Topology.Algebra.InfiniteSum.Real
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummable

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Summed Cauchy--Schwarz for the square-root graph-energy terms.

This passes from the already-proved finite-prefix Cauchy inequality to `tsum`
using `Real.tsum_le_of_sum_le`, whose mathlib source has the exact form

`Real.tsum_le_of_sum_le (hf : 0 ≤ f) (h : ∀ u : Finset ι, ∑ x ∈ u, f x ≤ c)`.
-/
theorem concrete_l2_summed_sqrt_energy_cauchy
    (p q : ConcreteL2GraphPairSpace) :
    (∑' n : ℕ,
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)) ≤
      Real.sqrt (concreteL2CompletedGraphEnergy p) *
        Real.sqrt (concreteL2CompletedGraphEnergy q) := by
  unfold concreteL2CompletedGraphEnergy
  have hp : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm p n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable p
  have hq : Summable fun n : ℕ => concreteL2GraphPairEnergyTerm q n :=
    concrete_l2_mathlib_spectral_audit_r2_graph_energy_summable q
  refine Real.tsum_le_of_sum_le
    (fun n : ℕ => concrete_l2_sqrt_energy_product_nonneg p q n) ?_
  intro u
  have hfinite := concrete_l2_finite_prefix_sqrt_energy_cauchy p q u
  have hpu :
      Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm p n) ≤
        ∑' n : ℕ, concreteL2GraphPairEnergyTerm p n := by
    exact hp.sum_le_tsum u (fun n hn => concrete_l2_graph_pair_energy_term_nonneg p n)
  have hqu :
      Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm q n) ≤
        ∑' n : ℕ, concreteL2GraphPairEnergyTerm q n := by
    exact hq.sum_le_tsum u (fun n hn => concrete_l2_graph_pair_energy_term_nonneg q n)
  have hsqrtp :
      Real.sqrt (Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm p n)) ≤
        Real.sqrt (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) :=
    Real.sqrt_le_sqrt hpu
  have hsqrtq :
      Real.sqrt (Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm q n)) ≤
        Real.sqrt (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n) :=
    Real.sqrt_le_sqrt hqu
  have hmul :
      Real.sqrt (Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm p n)) *
          Real.sqrt (Finset.sum u (fun n : ℕ => concreteL2GraphPairEnergyTerm q n)) ≤
        Real.sqrt (∑' n : ℕ, concreteL2GraphPairEnergyTerm p n) *
          Real.sqrt (∑' n : ℕ, concreteL2GraphPairEnergyTerm q n) := by
    exact mul_le_mul hsqrtp hsqrtq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hfinite.trans hmul

/-- Package: summed Cauchy--Schwarz for square-root graph-energy terms. -/
def concreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchy : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    (∑' n : ℕ,
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n)) ≤
      Real.sqrt (concreteL2CompletedGraphEnergy p) *
        Real.sqrt (concreteL2CompletedGraphEnergy q)

/-- The summed Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy :
    concreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchy := by
  intro p q
  exact concrete_l2_summed_sqrt_energy_cauchy p q

/-- Surface for summed square-root energy Cauchy. -/
structure ConcreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurface where
  productSummableReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurfaceReady
  summedCauchy : concreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchy
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete summed square-root energy Cauchy surface. -/
def concreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurface :
    ConcreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurface :=
  { productSummableReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summable_surface_ready
    summedCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for summed square-root energy Cauchy. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2SqrtEnergyProductSummableSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2SummedSqrtEnergyCauchy

/-- Readiness theorem for summed square-root energy Cauchy. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2SummedSqrtEnergyCauchySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_sqrt_energy_product_summable_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_summed_sqrt_energy_cauchy⟩

end

end MathlibAnalytic
end MGAP4D
