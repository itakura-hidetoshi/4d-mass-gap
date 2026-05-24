import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTriangleNextPRBoundary

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Pre-triangle surface for the graph-norm candidate.

This packages exactly the analytic material available before the true triangle
inequality: nonnegativity, zero law, absolute homogeneity, completed-energy
add-control, squared candidate add-control, and the sqrt-form candidate
add-bound.

It intentionally does not assert
`candidate(p + q) ≤ candidate p + candidate q`.
-/
def concreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTriangleNextPRBoundarySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateNonneg ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateZeroLaw ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateAbsHomogeneity ∧
  concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBound

/-- Readiness theorem for the graph-norm candidate pre-triangle surface. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_triangle_pre_surface_ready :
    concreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurfaceReady := by
  unfold concreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_triangle_next_pr_boundary_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_nonneg,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_zero_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_abs_homogeneity,
    concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_sqrt_add_bound⟩

/--
The remaining gap for true triangle inequality is explicit: the current
available bound is the sqrt-form pre-triangle estimate, not the Minkowski bound.
-/
def concreteL2MathlibSpectralAuditR2GraphNormTriangleRemainingGap : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ≤
      Real.sqrt
        ((2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
          (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2)

/-- The remaining triangle gap is backed by the inherited sqrt-form add-bound. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_triangle_remaining_gap_ready :
    concreteL2MathlibSpectralAuditR2GraphNormTriangleRemainingGap := by
  exact concrete_l2_graph_norm_candidate_add_le_sqrt_bound

/--
A structured record of the pre-triangle data available for the next analytic
step.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurface where
  boundaryReady : concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTriangleNextPRBoundarySurfaceReady
  nonneg : concreteL2MathlibSpectralAuditR2GraphNormCandidateNonneg
  zeroLaw : concreteL2MathlibSpectralAuditR2GraphNormCandidateZeroLaw
  absHomogeneity : concreteL2MathlibSpectralAuditR2GraphNormCandidateAbsHomogeneity
  completedEnergyAddBound : concreteL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound
  candidateAddSquareBound : concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound
  sqrtAddBound : concreteL2MathlibSpectralAuditR2GraphNormCandidateSqrtAddBound
  remainingGap : concreteL2MathlibSpectralAuditR2GraphNormTriangleRemainingGap
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete pre-triangle surface for the graph-norm candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTrianglePreSurface :=
  { boundaryReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_triangle_next_pr_boundary_surface_ready
    nonneg := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_nonneg
    zeroLaw := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_zero_law
    absHomogeneity := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_abs_homogeneity
    completedEnergyAddBound := concrete_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound
    candidateAddSquareBound := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound
    sqrtAddBound := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_sqrt_add_bound
    remainingGap := concrete_l2_mathlib_spectral_audit_r2_graph_norm_triangle_remaining_gap_ready
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True
    boundaryNotCore := True }

end

end MathlibAnalytic
end MGAP4D
