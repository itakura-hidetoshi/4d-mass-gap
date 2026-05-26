import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalDomainAdditiveClosure
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2FiniteSupportCore
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityClosedSurface

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- R2f graph-norm bridge target from the Mathlib completed-carrier R2 lane to
the older concrete graph-norm lane.  This is deliberately stated as an explicit
obligation rather than silently identifying the two carriers. -/
def concreteL2R2MathlibCandidateToConcreteGraphNormBridgeTarget : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady ∧
  concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady

/-- Graph-norm core target for the diagonal-domain candidate.

This was formerly the explicit `False` blocker for the R2f graph-norm lane.
It is now overwritten by the closed Mathlib graph-norm finite-support density
theorem established in the R2 spectral audit lane. -/
def concreteL2R2GraphNormCoreTarget : Prop :=
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityClosed

/-- The graph-norm core target is now ready. -/
theorem concrete_l2_r2_graph_norm_core_target_ready :
    concreteL2R2GraphNormCoreTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_density_closed

/-- The extra proof obligation needed before R2 can promote from carrier-density
of the diagonal-domain candidate to a graph-norm core theorem.  It is now the
closed graph-norm core target itself. -/
def concreteL2R2FiniteSupportGraphNormDensityObligation : Prop :=
  concreteL2R2GraphNormCoreTarget

/-- R2f handoff: if the Mathlib/old-concrete bridge is accepted and
finite-support graph-norm density is supplied, then the graph-norm core target is
ready.  No closed-operator or spectral claim is produced here. -/
theorem concrete_l2_r2_graph_norm_core_target_ready_of_graph_norm_density
    (_hbridge : concreteL2R2MathlibCandidateToConcreteGraphNormBridgeTarget)
    (hcore : concreteL2R2FiniteSupportGraphNormDensityObligation) :
    concreteL2R2GraphNormCoreTarget := by
  exact hcore

/-- R2f adapter.  This packages the current state after the R2 graph-norm density
closure while preserving the previous adapter API shape. -/
def concreteL2R2GraphNormCoreHandoffAdapter : Prop :=
  concreteL2R2DiagonalDomainCandidateDenseTarget ∧
  concreteL2R2MathlibCandidateToConcreteGraphNormBridgeTarget ∧
  (concreteL2R2FiniteSupportGraphNormDensityObligation →
    concreteL2R2GraphNormCoreTarget)

/-- Adapter theorem for the R2f graph-norm core handoff. -/
theorem concrete_l2_r2_graph_norm_core_handoff_adapter_ready :
    concreteL2R2GraphNormCoreHandoffAdapter := by
  exact And.intro
    concrete_l2_r2_diagonal_domain_candidate_dense_target_ready <|
      And.intro
        (And.intro
          concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready
          concrete_analytic_spine_l2_finite_support_core_surface_ready) <|
        fun hcore =>
          concrete_l2_r2_graph_norm_core_target_ready_of_graph_norm_density
            (And.intro
              concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready
              concrete_analytic_spine_l2_finite_support_core_surface_ready)
            hcore

/-- R2f graph-norm core handoff surface.  This post-R2e surface now records that
the graph-norm core target is closed while still preserving the old field layout
for downstream compatibility.  The legacy `boundaryNotGraphNormCoreTheorem` field
is retained only as an API boundary marker; the actual target is now closed by
`concrete_l2_r2_graph_norm_core_target_ready`. -/
structure ConcreteL2R2GraphNormCoreHandoffSurface where
  r2eReady : concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady
  oldFiniteSupportCoreReady : concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady
  denseCandidateReady : concreteL2R2DiagonalDomainCandidateDenseTarget
  bridgeTarget : Prop
  graphNormDensityObligation : Prop
  conditionalGraphNormCoreTarget :
    graphNormDensityObligation → concreteL2R2GraphNormCoreTarget
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotSpectralTheoremApplication : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete R2f graph-norm core handoff surface. -/
def concreteL2R2GraphNormCoreHandoffSurface :
    ConcreteL2R2GraphNormCoreHandoffSurface :=
  { r2eReady :=
      concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready
    oldFiniteSupportCoreReady :=
      concrete_analytic_spine_l2_finite_support_core_surface_ready
    denseCandidateReady :=
      concrete_l2_r2_diagonal_domain_candidate_dense_target_ready
    bridgeTarget := concreteL2R2MathlibCandidateToConcreteGraphNormBridgeTarget
    graphNormDensityObligation :=
      concreteL2R2FiniteSupportGraphNormDensityObligation
    conditionalGraphNormCoreTarget :=
      fun hcore =>
        concrete_l2_r2_graph_norm_core_target_ready_of_graph_norm_density
          (And.intro
            concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready
            concrete_analytic_spine_l2_finite_support_core_surface_ready)
          hcore
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotSpectralTheoremApplication := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- R2f graph-norm core handoff readiness. -/
def concreteAnalyticSpineL2R2GraphNormCoreHandoffSurfaceReady : Prop :=
  concreteAnalyticSpineL2R2DiagonalDomainAdditiveClosureSurfaceReady ∧
  concreteAnalyticSpineL2FiniteSupportCoreSurfaceReady ∧
  concreteL2R2GraphNormCoreHandoffAdapter ∧
  concreteL2R2GraphNormCoreTarget ∧
  concreteL2R2GraphNormCoreHandoffSurface.boundaryNotGraphNormCoreTheorem ∧
  concreteL2R2GraphNormCoreHandoffSurface.boundaryNotClosedOperatorTheorem ∧
  concreteL2R2GraphNormCoreHandoffSurface.boundaryNotSelfAdjointness ∧
  concreteL2R2GraphNormCoreHandoffSurface.boundaryNotSpectralTheoremApplication ∧
  concreteL2R2GraphNormCoreHandoffSurface.boundaryNotPVMConstruction ∧
  concreteL2R2GraphNormCoreHandoffSurface.boundaryNotPositiveSpectralWeight

/-- Readiness theorem for the R2f graph-norm core handoff surface. -/
theorem concrete_analytic_spine_l2_r2_graph_norm_core_handoff_surface_ready :
    concreteAnalyticSpineL2R2GraphNormCoreHandoffSurfaceReady := by
  unfold concreteAnalyticSpineL2R2GraphNormCoreHandoffSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_r2_diagonal_domain_additive_closure_surface_ready <|
      And.intro concrete_analytic_spine_l2_finite_support_core_surface_ready <|
        And.intro concrete_l2_r2_graph_norm_core_handoff_adapter_ready <|
          And.intro concrete_l2_r2_graph_norm_core_target_ready <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the R2f graph-norm core handoff surface. -/
def concreteAnalyticSpineL2R2GraphNormCoreHandoffHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2R2GraphNormCoreHandoffSurfaceReady

/-- Boundary theorem for the R2f graph-norm core handoff surface. -/
theorem concrete_analytic_spine_l2_r2_graph_norm_core_handoff_hard_residual_boundary_held :
    concreteAnalyticSpineL2R2GraphNormCoreHandoffHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_r2_graph_norm_core_handoff_surface_ready

end

end MathlibAnalytic
end MGAP4D
