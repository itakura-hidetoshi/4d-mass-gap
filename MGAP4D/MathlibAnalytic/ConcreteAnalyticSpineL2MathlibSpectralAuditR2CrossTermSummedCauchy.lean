import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummable

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Summed Cauchy--Schwarz for the signed cross-term series.

The signed cross-term series is summable, the square-root product series is
summable, and the pointwise cross-term Cauchy estimate gives the termwise upper
bound.  Therefore `tsum_le_tsum` yields the summed cross-term bound, and the
already-proved summed square-root energy Cauchy estimate closes the result.
-/
theorem concrete_l2_cross_term_summed_cauchy
    (p q : ConcreteL2GraphPairSpace) :
    (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) ≤
      Real.sqrt (concreteL2CompletedGraphEnergy p) *
        Real.sqrt (concreteL2CompletedGraphEnergy q) := by
  have hcross : Summable fun n : ℕ => concreteL2GraphPairCrossTerm p q n :=
    concrete_l2_graph_pair_cross_term_summable p q
  have hprod : Summable fun n : ℕ =>
      Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
        Real.sqrt (concreteL2GraphPairEnergyTerm q n) :=
    concrete_l2_sqrt_energy_product_summable p q
  have hpoint : ∀ n : ℕ,
      concreteL2GraphPairCrossTerm p q n ≤
        Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
          Real.sqrt (concreteL2GraphPairEnergyTerm q n) := by
    intro n
    exact concrete_l2_graph_pair_cross_term_pointwise_cauchy p q n
  have hle_product :
      (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) ≤
        ∑' n : ℕ,
          Real.sqrt (concreteL2GraphPairEnergyTerm p n) *
            Real.sqrt (concreteL2GraphPairEnergyTerm q n) := by
    exact hcross.tsum_le_tsum hpoint hprod
  exact hle_product.trans (concrete_l2_summed_sqrt_energy_cauchy p q)

/-- Package: summed Cauchy--Schwarz for the signed cross-term series. -/
def concreteL2MathlibSpectralAuditR2CrossTermSummedCauchy : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    (∑' n : ℕ, concreteL2GraphPairCrossTerm p q n) ≤
      Real.sqrt (concreteL2CompletedGraphEnergy p) *
        Real.sqrt (concreteL2CompletedGraphEnergy q)

/-- The summed cross-term Cauchy package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy :
    concreteL2MathlibSpectralAuditR2CrossTermSummedCauchy := by
  intro p q
  exact concrete_l2_cross_term_summed_cauchy p q

/-- Surface for summed cross-term Cauchy. -/
structure ConcreteL2MathlibSpectralAuditR2CrossTermSummedCauchySurface where
  signedSummableReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummableSurfaceReady
  summedCrossCauchy : concreteL2MathlibSpectralAuditR2CrossTermSummedCauchy
  boundaryNotMinkowskiSquare : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete surface for summed cross-term Cauchy. -/
def concreteL2MathlibSpectralAuditR2CrossTermSummedCauchySurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermSummedCauchySurface :=
  { signedSummableReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_signed_summable_surface_ready
    summedCrossCauchy :=
      concrete_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy
    boundaryNotMinkowskiSquare := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for summed cross-term Cauchy. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummableSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CrossTermSummedCauchy

/-- Readiness theorem for summed cross-term Cauchy. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSummedCauchySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_signed_summable_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_cross_term_summed_cauchy⟩

end

end MathlibAnalytic
end MGAP4D
