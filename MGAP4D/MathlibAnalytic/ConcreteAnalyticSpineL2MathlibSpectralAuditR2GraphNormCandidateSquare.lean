import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidate

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
The square of the graph-norm candidate recovers the completed graph energy.

This is a genuine bridge from the `sqrt` candidate back to the completed
square-energy functional.  It uses nonnegativity of completed graph energy and
`Real.sq_sqrt`.
-/
theorem concrete_l2_graph_norm_candidate_sq
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate p ^ 2 = concreteL2CompletedGraphEnergy p := by
  unfold concreteL2GraphNormCandidate
  exact Real.sq_sqrt (concrete_l2_completed_graph_energy_nonneg p)

/-- Squared graph-norm candidate package. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateSquareLaw : Prop :=
  ∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate p ^ 2 = concreteL2CompletedGraphEnergy p

/-- The squared graph-norm candidate law is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_law :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateSquareLaw := by
  exact concrete_l2_graph_norm_candidate_sq

/--
Graph-norm candidate surface with square-recovery law.

The candidate is now tied back to the completed square-energy functional.  This
still does not prove triangle inequality or define a topology.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCandidateSquareSurface where
  candidateReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSurfaceReady
  graphNormCandidate : ConcreteL2GraphPairSpace → ℝ
  completedEnergy : ConcreteL2GraphPairSpace → ℝ
  candidate_eq_sqrt : ∀ p : ConcreteL2GraphPairSpace,
    graphNormCandidate p = Real.sqrt (completedEnergy p)
  squareLaw : ∀ p : ConcreteL2GraphPairSpace,
    graphNormCandidate p ^ 2 = completedEnergy p
  nonneg : ∀ p : ConcreteL2GraphPairSpace, 0 ≤ graphNormCandidate p
  zeroLaw : graphNormCandidate concreteL2GraphPairZero = 0
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop

/-- Concrete graph-norm candidate square surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateSquareSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCandidateSquareSurface :=
  { candidateReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_surface_ready
    graphNormCandidate := concreteL2GraphNormCandidate
    completedEnergy := concreteL2CompletedGraphEnergy
    candidate_eq_sqrt := fun _p => rfl
    squareLaw := concrete_l2_graph_norm_candidate_sq
    nonneg := concrete_l2_graph_norm_candidate_nonneg
    zeroLaw := concrete_l2_graph_norm_candidate_zero
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True }

/-- Readiness predicate for the graph-norm candidate square surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateSquareLaw ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateNonneg ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateZeroLaw

/-- Readiness theorem for the graph-norm candidate square surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSquareSurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_square_law,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_nonneg,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_zero_law⟩

end

end MathlibAnalytic
end MGAP4D
