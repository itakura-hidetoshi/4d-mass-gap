import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidate

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Explicit graph-pair subtraction is antisymmetric up to explicit negation. -/
theorem concrete_l2_graph_pair_sub_eq_neg_sub_rev
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSub p q =
      concreteL2GraphPairNeg (concreteL2GraphPairSub q p) := by
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

/-- Symmetry of the graph-norm distance candidate. -/
theorem concrete_l2_graph_norm_distance_candidate_symm
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormDistanceCandidate p q =
      concreteL2GraphNormDistanceCandidate q p := by
  unfold concreteL2GraphNormDistanceCandidate
  rw [concrete_l2_graph_pair_sub_eq_neg_sub_rev p q]
  exact concrete_l2_graph_norm_candidate_neg (concreteL2GraphPairSub q p)

/-- Package: symmetry of the graph-norm distance candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateSymmetry : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormDistanceCandidate p q =
      concreteL2GraphNormDistanceCandidate q p

/-- The graph-norm distance candidate symmetry package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_symmetry :
    concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateSymmetry := by
  intro p q
  exact concrete_l2_graph_norm_distance_candidate_symm p q

/-- Surface for symmetry of the graph-norm distance candidate. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurface where
  distanceCandidateReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurfaceReady
  subAntisymmetry : ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphPairSub p q = concreteL2GraphPairNeg (concreteL2GraphPairSub q p)
  distanceSymmetry : concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateSymmetry
  boundaryNotDistanceTriangle : Prop
  boundaryNotPseudoMetricTopology : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete surface for symmetry of the graph-norm distance candidate. -/
def concreteL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurface :=
  { distanceCandidateReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_pair_neg_sub_distance_candidate_surface_ready
    subAntisymmetry := concrete_l2_graph_pair_sub_eq_neg_sub_rev
    distanceSymmetry :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_symmetry
    boundaryNotDistanceTriangle := True
    boundaryNotPseudoMetricTopology := True
    boundaryNotDensity := True
    boundaryNotCore := True }

/-- Readiness predicate for graph-norm distance symmetry. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateSymmetry

/-- Readiness theorem for graph-norm distance symmetry. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_distance_symmetry_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceSymmetrySurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_pair_neg_sub_distance_candidate_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_symmetry⟩

end

end MathlibAnalytic
end MGAP4D
