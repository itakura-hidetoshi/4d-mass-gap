import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceSymmetry

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Explicit subtraction cocycle identity for concrete graph pairs.

This is the algebraic identity behind the distance triangle inequality:
`p - r = (p - q) + (q - r)`.
-/
theorem concrete_l2_graph_pair_sub_cocycle
    (p q r : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSub p r =
      concreteL2GraphPairAdd (concreteL2GraphPairSub p q) (concreteL2GraphPairSub q r) := by
  unfold concreteL2GraphPairSub concreteL2GraphPairNeg concreteL2GraphPairAdd
  unfold concreteL2GraphPairSmul
  apply Prod.ext
  · apply Subtype.ext
    funext n
    simp [concreteL2RealAdd, concreteL2RealSmul]
    ring
  · apply Subtype.ext
    funext n
    simp [concreteL2RealAdd, concreteL2RealSmul]
    ring

/-- Triangle inequality for the graph-norm distance candidate. -/
theorem concrete_l2_graph_norm_distance_candidate_triangle
    (p q r : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormDistanceCandidate p r ≤
      concreteL2GraphNormDistanceCandidate p q +
        concreteL2GraphNormDistanceCandidate q r := by
  unfold concreteL2GraphNormDistanceCandidate
  rw [concrete_l2_graph_pair_sub_cocycle p q r]
  exact concrete_l2_graph_norm_candidate_triangle
    (concreteL2GraphPairSub p q) (concreteL2GraphPairSub q r)

/-- Package: triangle inequality for the graph-norm distance candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateTriangle : Prop :=
  ∀ p q r : ConcreteL2GraphPairSpace,
    concreteL2GraphNormDistanceCandidate p r ≤
      concreteL2GraphNormDistanceCandidate p q +
        concreteL2GraphNormDistanceCandidate q r

/-- The graph-norm distance candidate triangle package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_triangle :
    concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateTriangle := by
  intro p q r
  exact concrete_l2_graph_norm_distance_candidate_triangle p q r

/-- Surface for the graph-norm distance candidate triangle inequality. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormDistanceTriangleSurface where
  distanceSymmetryReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurfaceReady
  subCocycle : ∀ p q r : ConcreteL2GraphPairSpace,
    concreteL2GraphPairSub p r =
      concreteL2GraphPairAdd (concreteL2GraphPairSub p q) (concreteL2GraphPairSub q r)
  distanceTriangle : concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateTriangle
  boundaryNotPseudoMetricTopology : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete surface for the graph-norm distance candidate triangle inequality. -/
def concreteL2MathlibSpectralAuditR2GraphNormDistanceTriangleSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormDistanceTriangleSurface :=
  { distanceSymmetryReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_distance_symmetry_surface_ready
    subCocycle := concrete_l2_graph_pair_sub_cocycle
    distanceTriangle :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_triangle
    boundaryNotPseudoMetricTopology := True
    boundaryNotDensity := True
    boundaryNotCore := True }

/-- Readiness predicate for graph-norm distance candidate triangle. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceTriangleSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateTriangle

/-- Readiness theorem for graph-norm distance candidate triangle. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_distance_triangle_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceTriangleSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_distance_symmetry_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_triangle⟩

end

end MathlibAnalytic
end MGAP4D
