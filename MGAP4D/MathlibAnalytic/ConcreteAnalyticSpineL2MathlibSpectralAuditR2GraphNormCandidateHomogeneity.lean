import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSmulSquare

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/--
Absolute-value homogeneity of the graph-norm candidate under the explicit graph
scalar operation.

This is still a candidate-level theorem, not a `NormedAddCommGroup` instance and
not a graph-norm topology.  The proof uses the squared scalar law plus
nonnegativity of both sides.
-/
theorem concrete_l2_graph_norm_candidate_smul_abs
    (c : ℝ) (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairSmul c p) =
      |c| * concreteL2GraphNormCandidate p := by
  let a := concreteL2GraphNormCandidate (concreteL2GraphPairSmul c p)
  let b := |c| * concreteL2GraphNormCandidate p
  have ha : 0 ≤ a := by
    dsimp [a]
    exact concrete_l2_graph_norm_candidate_nonneg (concreteL2GraphPairSmul c p)
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (abs_nonneg c) (concrete_l2_graph_norm_candidate_nonneg p)
  have hsq0 : a ^ 2 = c ^ 2 * concreteL2GraphNormCandidate p ^ 2 := by
    dsimp [a]
    exact concrete_l2_graph_norm_candidate_smul_sq c p
  have hb_sq : b ^ 2 = c ^ 2 * concreteL2GraphNormCandidate p ^ 2 := by
    dsimp [b]
    rw [mul_pow]
    rw [sq_abs]
  have hsq : a ^ 2 = b ^ 2 := by
    rw [hsq0, hb_sq]
  have hab : a = b := by
    nlinarith
  exact hab

/-- Absolute-value homogeneity package for the graph-norm candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateAbsHomogeneity : Prop :=
  ∀ (c : ℝ) (p : ConcreteL2GraphPairSpace),
    concreteL2GraphNormCandidate (concreteL2GraphPairSmul c p) =
      |c| * concreteL2GraphNormCandidate p

/-- The absolute-value homogeneity package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_abs_homogeneity :
    concreteL2MathlibSpectralAuditR2GraphNormCandidateAbsHomogeneity := by
  exact concrete_l2_graph_norm_candidate_smul_abs

/--
Graph-norm candidate surface with absolute-value homogeneity.

Triangle inequality, topology, density, and core remain downstream.
-/
structure ConcreteL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurface where
  smulSquareReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurfaceReady
  absHomogeneity : concreteL2MathlibSpectralAuditR2GraphNormCandidateAbsHomogeneity
  nonneg : concreteL2MathlibSpectralAuditR2GraphNormCandidateNonneg
  zeroLaw : concreteL2MathlibSpectralAuditR2GraphNormCandidateZeroLaw
  boundaryNotTriangleInequality : Prop
  boundaryNotTopology : Prop
  boundaryNotDensity : Prop

/-- Concrete graph-norm candidate homogeneity surface. -/
def concreteL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurface :=
  { smulSquareReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_smul_square_surface_ready
    absHomogeneity :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_abs_homogeneity
    nonneg := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_nonneg
    zeroLaw := concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_zero_law
    boundaryNotTriangleInequality := True
    boundaryNotTopology := True
    boundaryNotDensity := True }

/-- Readiness predicate for the graph-norm candidate homogeneity surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateSmulSquareSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateAbsHomogeneity ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateNonneg ∧
  concreteL2MathlibSpectralAuditR2GraphNormCandidateZeroLaw

/-- Readiness theorem for the graph-norm candidate homogeneity surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_homogeneity_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormCandidateHomogeneitySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_candidate_smul_square_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_abs_homogeneity,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_nonneg,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_candidate_zero_law⟩

end

end MathlibAnalytic
end MGAP4D
