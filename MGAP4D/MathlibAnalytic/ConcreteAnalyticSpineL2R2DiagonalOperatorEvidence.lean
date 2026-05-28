import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalGraphNorm
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalDomainAdditiveClosure
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2UnitObstructionBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- R2 diagonal operator evidence surface.

This surface uses the concrete diagonal action `x ↦ ((n+1) x_n)_n` and records
its graph carrier, dense diagonal-domain candidate, and unit-probe growth law. -/
def concreteL2R2DiagonalOperatorEvidence : Prop :=
  concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady ∧
  concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady ∧
  concreteL2R2DiagonalDomainCandidateDenseTarget ∧
  (∀ k : ℕ,
    (k : ℝ) <
      concreteL2DiagonalRawAction (concreteL2ObstructionUnitDomain k)
        (concreteL2DiagonalUnboundednessObstructionSurface.witness k)) ∧
  True ∧ True ∧ True ∧ True

/-- The R2 diagonal operator evidence surface follows from the existing diagonal
graph, dense-domain, and unit-probe layers. -/
theorem concrete_l2_r2_diagonal_operator_evidence :
    concreteL2R2DiagonalOperatorEvidence := by
  exact ⟨
    concrete_analytic_spine_l2_diagonal_graph_norm_surface_ready,
    concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready,
    concrete_l2_r2_diagonal_domain_candidate_dense_target_ready,
    concrete_l2_obstruction_unit_action_threshold_law,
    trivial,
    trivial,
    trivial,
    trivial⟩

/-- Public theorem-entry predicate for the R2 diagonal operator evidence layer. -/
def concreteAnalyticSpineL2R2DiagonalOperatorEvidenceReady : Prop :=
  concreteL2R2DiagonalOperatorEvidence

/-- The R2 diagonal operator evidence layer is ready. -/
theorem concrete_analytic_spine_l2_r2_diagonal_operator_evidence_ready :
    concreteAnalyticSpineL2R2DiagonalOperatorEvidenceReady := by
  exact concrete_l2_r2_diagonal_operator_evidence

end

end MathlibAnalytic
end MGAP4D
