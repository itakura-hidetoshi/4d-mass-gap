import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchy

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Summability of the absolute cross-term series.

This uses the absolute pointwise Cauchy estimate and the already-proved
summability of the square-root energy product.  It deliberately proves absolute
summability first, since the cross term is signed.
-/
theorem concrete_l2_graph_pair_cross_term_abs_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ => |concreteL2GraphPairCrossTerm p q n| := by
  refine Summable.of_nonneg_of_le
    (fun n : ℕ => abs_nonneg (concreteL2GraphPairCrossTerm p q n))
    (fun n : ℕ => concrete_l2_graph_pair_cross_term_abs_pointwise_cauchy p q n)
    (concrete_l2_sqrt_energy_product_summable p q)

/-- Package: absolute summability of the cross-term series. -/
def concreteL2MathlibSpectralAuditR2CrossTermAbsSummable : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    Summable fun n : ℕ => |concreteL2GraphPairCrossTerm p q n|

/-- The absolute cross-term summability package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_abs_summable :
    concreteL2MathlibSpectralAuditR2CrossTermAbsSummable := by
  intro p q
  exact concrete_l2_graph_pair_cross_term_abs_summable p q

/--
Surface for absolute cross-term summability.
-/
structure ConcreteL2MathlibSpectralAuditR2CrossTermAbsSummableSurface where
  absPointwiseReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurfaceReady
  absSummable : concreteL2MathlibSpectralAuditR2CrossTermAbsSummable
  boundaryNotSignedCrossTermSummable : Prop
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete absolute cross-term summability surface. -/
def concreteL2MathlibSpectralAuditR2CrossTermAbsSummableSurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermAbsSummableSurface :=
  { absPointwiseReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_abs_pointwise_cauchy_surface_ready
    absSummable :=
      concrete_l2_mathlib_spectral_audit_r2_cross_term_abs_summable
    boundaryNotSignedCrossTermSummable := True
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for absolute cross-term summability. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsSummableSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsPointwiseCauchySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CrossTermAbsSummable

/-- Readiness theorem for absolute cross-term summability. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_abs_summable_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermAbsSummableSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_abs_pointwise_cauchy_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_cross_term_abs_summable⟩

end

end MathlibAnalytic
end MGAP4D
