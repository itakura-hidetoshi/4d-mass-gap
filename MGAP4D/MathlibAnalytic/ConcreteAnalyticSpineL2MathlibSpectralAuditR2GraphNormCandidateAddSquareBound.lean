import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyAddBound

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Squared add-control for the graph-norm candidate.

This is the candidate-level lift of the completed-energy add bound.  It is a
pre-triangle estimate: it does not assert the graph-norm triangle inequality,
but it transfers the completed square-energy control to the square of the
candidate.
-/
theorem concrete_l2_graph_norm_candidate_add_sq_le
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ^ 2 ≤
      (2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
        (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2 := by
  calc
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ^ 2
        = concreteL2CompletedGraphEnergy (concreteL2GraphPairAdd p q) := by
          exact concrete_l2_graph_norm_candidate_sq (concreteL2GraphPairAdd p q)
    _ ≤ (2 : ℝ) * concreteL2CompletedGraphEnergy p +
          (2 : ℝ) * concreteL2CompletedGraphEnergy q := by
          exact concrete_l2_completed_graph_energy_add_le p q
    _ = (2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
          (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2 := by
          rw [concrete_l2_graph_norm_candidate_sq p,
              concrete_l2_graph_norm_candidate_sq q]

/-- Candidate squared add-control package. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate (concreteL2GraphPairAdd p q) ^ 2 ≤
      (2 : ℝ) * concreteL2GraphNormCandidate p ^ 2 +
        (2 : ℝ) * concreteL2GraphNormCandidate q ^ 2

/-- The candidate squared add-control package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound := by
  exact concrete_l2_graph_norm_candidate_add_sq_le

/--
Graph-norm candidate surface with squared add-control.

This is still below the true triangle inequality and below any topology or core
claim.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurface where
  completedAddBoundReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurfaceReady
  homogeneityReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurfaceReady
  addSquareBound : concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop

/-- Concrete candidate squared add-control surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurface :=
  { completedAddBoundReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound_surface_ready
    homogeneityReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_homogeneity_surface_ready
    addSquareBound :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True }

/-- Readiness predicate for the candidate squared add-control surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergyAddBoundSurfaceReady ∧
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBound

/-- Readiness theorem for the candidate squared add-control surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateAddSquareBoundSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_add_bound_surface_ready,
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_homogeneity_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_add_square_bound⟩

end

end MathlibAnalytic
end MGAP4D
