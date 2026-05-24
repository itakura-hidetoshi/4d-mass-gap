import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Summability of the positive part of the cross-term series. -/
theorem concrete_l2_graph_pair_cross_term_pos_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ => concreteL2GraphPairCrossTermPos p q n := by
  refine Summable.of_nonneg_of_le
    (fun n : ℕ => concrete_l2_graph_pair_cross_term_pos_nonneg p q n)
    (fun n : ℕ => concrete_l2_graph_pair_cross_term_pos_le_abs p q n)
    (concrete_l2_graph_pair_cross_term_abs_summable p q)

/-- Summability of the negative part of the cross-term series. -/
theorem concrete_l2_graph_pair_cross_term_neg_summable
    (p q : ConcreteL2GraphPairSpace) :
    Summable fun n : ℕ => concreteL2GraphPairCrossTermNeg p q n := by
  refine Summable.of_nonneg_of_le
    (fun n : ℕ => concrete_l2_graph_pair_cross_term_neg_nonneg p q n)
    (fun n : ℕ => concrete_l2_graph_pair_cross_term_neg_le_abs p q n)
    (concrete_l2_graph_pair_cross_term_abs_summable p q)

/-- Package: summability of both positive and negative cross-term parts. -/
def concreteL2MathlibSpectralAuditR2CrossTermPosNegSummable : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    (Summable fun n : ℕ => concreteL2GraphPairCrossTermPos p q n) ∧
      (Summable fun n : ℕ => concreteL2GraphPairCrossTermNeg p q n)

/-- The positive/negative cross-term summability package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_cross_term_pos_neg_summable :
    concreteL2MathlibSpectralAuditR2CrossTermPosNegSummable := by
  intro p q
  exact ⟨
    concrete_l2_graph_pair_cross_term_pos_summable p q,
    concrete_l2_graph_pair_cross_term_neg_summable p q⟩

/-- Surface for positive/negative cross-term summability. -/
structure ConcreteL2MathlibSpectralAuditR2CrossTermPosNegSummableSurface where
  signedFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurfaceReady
  posNegSummable : concreteL2MathlibSpectralAuditR2CrossTermPosNegSummable
  boundaryNotSignedCrossTermSummable : Prop
  boundaryNotCrossTermSummedCauchy : Prop
  boundaryNotExactTriangle : Prop

/-- Concrete surface for positive/negative cross-term summability. -/
def concreteL2MathlibSpectralAuditR2CrossTermPosNegSummableSurface :
    ConcreteL2MathlibSpectralAuditR2CrossTermPosNegSummableSurface :=
  { signedFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_signed_summability_frontier_surface_ready
    posNegSummable :=
      concrete_l2_mathlib_spectral_audit_r2_cross_term_pos_neg_summable
    boundaryNotSignedCrossTermSummable := True
    boundaryNotCrossTermSummedCauchy := True
    boundaryNotExactTriangle := True }

/-- Readiness predicate for positive/negative cross-term summability. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermPosNegSummableSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermSignedSummabilityFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2CrossTermPosNegSummable

/-- Readiness theorem for positive/negative cross-term summability. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_pos_neg_summable_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CrossTermPosNegSummableSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_cross_term_signed_summability_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_cross_term_pos_neg_summable⟩

end

end MathlibAnalytic
end MGAP4D
