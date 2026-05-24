import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairTransport
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairLinearScaffold

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Spectral-audit bridge for the R2i graph-pair linear scaffold.

This layer exposes explicit add/smul operations on the concrete square-summable
sequence carrier and on graph pairs, together with fst/snd compatibility laws.
It still does not assert diagonal-graph closure, graph-norm density, closedness,
self-adjointness, or any spectral theorem.
-/
def concreteL2MathlibSpectralAuditR2GraphPairLinear : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairTransportSurfaceReady ∧
  concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady

/-- Readiness theorem for the spectral-audit R2i graph-pair linear bridge. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_ready :
    concreteL2MathlibSpectralAuditR2GraphPairLinear := by
  unfold concreteL2MathlibSpectralAuditR2GraphPairLinear
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_pair_transport_surface_ready,
    concrete_analytic_spine_l2_r2_graph_pair_linear_scaffold_ready⟩

/-- Explicit concrete `l2` add/smul operations are available. -/
def concreteL2MathlibSpectralAuditR2ConcreteL2LinearOpsReady : Prop :=
  Nonempty (ConcreteL2RealSequence → ConcreteL2RealSequence → ConcreteL2RealSequence) ∧
  Nonempty (ℝ → ConcreteL2RealSequence → ConcreteL2RealSequence)

/-- Concrete `l2` add/smul operation readiness. -/
theorem concrete_l2_mathlib_spectral_audit_r2_concrete_l2_linear_ops_ready :
    concreteL2MathlibSpectralAuditR2ConcreteL2LinearOpsReady := by
  exact ⟨⟨concreteL2RealAdd⟩, ⟨concreteL2RealSmul⟩⟩

/-- Explicit graph-pair add/smul operations are available. -/
def concreteL2MathlibSpectralAuditR2GraphPairLinearOpsReady : Prop :=
  Nonempty (ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace) ∧
  Nonempty (ℝ → ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace)

/-- Graph-pair add/smul operation readiness. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_ops_ready :
    concreteL2MathlibSpectralAuditR2GraphPairLinearOpsReady := by
  exact ⟨⟨concreteL2GraphPairAdd⟩, ⟨concreteL2GraphPairSmul⟩⟩

/-- First projection is compatible with graph-pair addition. -/
def concreteL2MathlibSpectralAuditR2GraphPairFstAddLaw : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphPairFst (concreteL2GraphPairAdd p q) =
      concreteL2RealAdd (concreteL2GraphPairFst p) (concreteL2GraphPairFst q)

/-- First projection addition law. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_fst_add_law :
    concreteL2MathlibSpectralAuditR2GraphPairFstAddLaw := by
  exact concrete_l2_graph_pair_fst_add

/-- Second projection is compatible with graph-pair addition. -/
def concreteL2MathlibSpectralAuditR2GraphPairSndAddLaw : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphPairSnd (concreteL2GraphPairAdd p q) =
      concreteL2RealAdd (concreteL2GraphPairSnd p) (concreteL2GraphPairSnd q)

/-- Second projection addition law. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_snd_add_law :
    concreteL2MathlibSpectralAuditR2GraphPairSndAddLaw := by
  exact concrete_l2_graph_pair_snd_add

/-- First projection is compatible with graph-pair scalar multiplication. -/
def concreteL2MathlibSpectralAuditR2GraphPairFstSmulLaw : Prop :=
  ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairFst (concreteL2GraphPairSmul c p) =
      concreteL2RealSmul c (concreteL2GraphPairFst p)

/-- First projection scalar law. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_fst_smul_law :
    concreteL2MathlibSpectralAuditR2GraphPairFstSmulLaw := by
  exact concrete_l2_graph_pair_fst_smul

/-- Second projection is compatible with graph-pair scalar multiplication. -/
def concreteL2MathlibSpectralAuditR2GraphPairSndSmulLaw : Prop :=
  ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphPairSnd (concreteL2GraphPairSmul c p) =
      concreteL2RealSmul c (concreteL2GraphPairSnd p)

/-- Second projection scalar law. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_snd_smul_law :
    concreteL2MathlibSpectralAuditR2GraphPairSndSmulLaw := by
  exact concrete_l2_graph_pair_snd_smul

/-- Hard residual boundary after the R2i graph-pair linear bridge. -/
def concreteL2MathlibSpectralAuditR2GraphPairLinearHardResidualBoundaryHeld : Prop :=
  concreteL2MathlibSpectralAuditR2GraphPairTransportHardResidualBoundaryHeld ∧
  concreteAnalyticSpineL2R2GraphPairLinearHardResidualBoundaryHeld

/-- Hard residual boundary theorem for the spectral-audit R2i graph-pair linear bridge. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_hard_residual_boundary_held :
    concreteL2MathlibSpectralAuditR2GraphPairLinearHardResidualBoundaryHeld := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_transport_hard_residual_boundary_held,
    concrete_analytic_spine_l2_r2_graph_pair_linear_hard_residual_boundary_held⟩

/-- Surface for the spectral-audit R2i graph-pair linear bridge. -/
structure ConcreteL2MathlibSpectralAuditR2GraphPairLinearSurface where
  graphPairTransportReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairTransportSurfaceReady
  r2GraphPairLinearReady :
    concreteAnalyticSpineL2R2GraphPairLinearScaffoldReady
  concreteL2LinearOpsReady : concreteL2MathlibSpectralAuditR2ConcreteL2LinearOpsReady
  graphPairLinearOpsReady : concreteL2MathlibSpectralAuditR2GraphPairLinearOpsReady
  fstAddLaw : concreteL2MathlibSpectralAuditR2GraphPairFstAddLaw
  sndAddLaw : concreteL2MathlibSpectralAuditR2GraphPairSndAddLaw
  fstSmulLaw : concreteL2MathlibSpectralAuditR2GraphPairFstSmulLaw
  sndSmulLaw : concreteL2MathlibSpectralAuditR2GraphPairSndSmulLaw
  diagonalGraphClosureObligation : Prop
  graphNormDensityObligation : Prop
  hardResidualBoundaryHeld : concreteL2MathlibSpectralAuditR2GraphPairLinearHardResidualBoundaryHeld

/-- Concrete spectral-audit R2i graph-pair linear surface. -/
def concreteL2MathlibSpectralAuditR2GraphPairLinearSurface :
    ConcreteL2MathlibSpectralAuditR2GraphPairLinearSurface :=
  { graphPairTransportReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_pair_transport_surface_ready
    r2GraphPairLinearReady :=
      concrete_analytic_spine_l2_r2_graph_pair_linear_scaffold_ready
    concreteL2LinearOpsReady :=
      concrete_l2_mathlib_spectral_audit_r2_concrete_l2_linear_ops_ready
    graphPairLinearOpsReady :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_ops_ready
    fstAddLaw :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_fst_add_law
    sndAddLaw :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_snd_add_law
    fstSmulLaw :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_fst_smul_law
    sndSmulLaw :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_snd_smul_law
    diagonalGraphClosureObligation :=
      concreteL2R2GraphPairLinearScaffold.boundaryNotDiagonalGraphAddClosure ∧
        concreteL2R2GraphPairLinearScaffold.boundaryNotDiagonalGraphSmulClosure
    graphNormDensityObligation :=
      concreteL2MathlibSpectralAuditR2GraphNormDensityObligation
    hardResidualBoundaryHeld :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_hard_residual_boundary_held }

/-- Readiness predicate for the spectral-audit R2i graph-pair linear surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairLinearSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2GraphPairLinear ∧
  concreteL2MathlibSpectralAuditR2ConcreteL2LinearOpsReady ∧
  concreteL2MathlibSpectralAuditR2GraphPairLinearOpsReady ∧
  concreteL2MathlibSpectralAuditR2GraphPairFstAddLaw ∧
  concreteL2MathlibSpectralAuditR2GraphPairSndAddLaw ∧
  concreteL2MathlibSpectralAuditR2GraphPairFstSmulLaw ∧
  concreteL2MathlibSpectralAuditR2GraphPairSndSmulLaw ∧
  concreteL2MathlibSpectralAuditR2GraphPairLinearHardResidualBoundaryHeld

/-- Readiness theorem for the spectral-audit R2i graph-pair linear surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_pair_linear_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairLinearSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairLinearSurfaceReady
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_ready,
    concrete_l2_mathlib_spectral_audit_r2_concrete_l2_linear_ops_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_ops_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_fst_add_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_snd_add_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_fst_smul_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_snd_smul_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_linear_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
