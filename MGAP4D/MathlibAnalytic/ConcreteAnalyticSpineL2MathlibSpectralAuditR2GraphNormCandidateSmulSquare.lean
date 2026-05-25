import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySmul

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Squared homogeneity of the graph-norm candidate.

This is the algebraic bridge immediately below full norm homogeneity.  It avoids
prematurely invoking a `Norm` instance or graph-norm topology: the claim is only
that the square of the candidate scales by `c^2`, using the completed-energy
scalar law and the square-recovery law.
-/
theorem concrete_l2_graph_norm_candidate_smul_sq
    (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairSmul c p) ^ 2 =
      (c ^ 2) * concreteL2GraphNormCandidate p ^ 2 := by
  calc
    concreteL2GraphNormCandidate (concreteL2GraphPairSmul c p) ^ 2
        = concreteL2CompletedGraphEnergy (concreteL2GraphPairSmul c p) := by
          exact concrete_l2_graph_norm_candidate_sq (concreteL2GraphPairSmul c p)
    _ = (c ^ 2) * concreteL2CompletedGraphEnergy p := by
          exact concrete_l2_completed_graph_energy_smul c p
    _ = (c ^ 2) * concreteL2GraphNormCandidate p ^ 2 := by
          rw [concrete_l2_graph_norm_candidate_sq p]

/-- Squared homogeneity package for the graph-norm candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareLaw : Prop :=
  ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphNormCandidate (concreteL2GraphPairSmul c p) ^ 2 =
      (c ^ 2) * concreteL2GraphNormCandidate p ^ 2

/-- The squared homogeneity package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_smul_square_law :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareLaw := by
  exact concrete_l2_graph_norm_candidate_smul_sq

/--
Graph-norm candidate surface with scalar square law.

This is still below the full absolute-value homogeneity theorem
`candidate(c • p) = |c| * candidate(p)`, and below topology/density/core.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurface where
  completedEnergySmulReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurfaceReady
  candidateSquareReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady
  smulSquareLaw : concreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareLaw
  boundaryNotAbsHomogeneity : Prop
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop

/-- Concrete graph-norm candidate scalar-square surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurface :=
  { completedEnergySmulReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_smul_surface_ready
    candidateSquareReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_surface_ready
    smulSquareLaw :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_smul_square_law
    boundaryNotAbsHomogeneity := True
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True }

/-- Readiness predicate for the graph-norm candidate scalar-square surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2CompletedGraphEnergySmulSurfaceReady ∧
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareLaw

/-- Readiness theorem for the graph-norm candidate scalar-square surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_smul_square_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_completed_graph_energy_smul_surface_ready,
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_smul_square_law⟩

end

end MathlibAnalytic
end MGAP4D
