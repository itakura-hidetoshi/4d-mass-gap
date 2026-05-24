import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceFrontier

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Explicit negation for concrete graph pairs, defined through the existing
scalar multiplication operation. -/
def concreteL2GraphPairNeg (p : ConcreteL2GraphPairSpace) : ConcreteL2GraphPairSpace :=
  concreteL2GraphPairSmul (-1 : ℝ) p

/-- Explicit subtraction for concrete graph pairs. -/
def concreteL2GraphPairSub
    (p q : ConcreteL2GraphPairSpace) : ConcreteL2GraphPairSpace :=
  concreteL2GraphPairAdd p (concreteL2GraphPairNeg q)

/-- Concrete graph-norm candidate is invariant under explicit negation. -/
theorem concrete_l2_graph_norm_candidate_neg
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormCandidate (concreteL2GraphPairNeg p) =
      concreteL2GraphNormCandidate p := by
  unfold concreteL2GraphPairNeg
  simpa using concrete_l2_graph_norm_candidate_smul_abs (-1 : ℝ) p

/-- Explicit subtraction of a graph pair from itself is the zero graph pair. -/
theorem concrete_l2_graph_pair_sub_self
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphPairSub p p = concreteL2GraphPairZero := by
  unfold concreteL2GraphPairSub concreteL2GraphPairNeg concreteL2GraphPairAdd
  unfold concreteL2GraphPairSmul concreteL2GraphPairZero
  apply Prod.ext
  · apply Subtype.ext
    funext n
    simp [concreteL2RealAdd, concreteL2RealSmul, concreteL2RealZero]
  · apply Subtype.ext
    funext n
    simp [concreteL2RealAdd, concreteL2RealSmul, concreteL2RealZero]

/-- Graph-norm distance candidate induced by explicit graph-pair subtraction. -/
def concreteL2GraphNormDistanceCandidate
    (p q : ConcreteL2GraphPairSpace) : ℝ :=
  concreteL2GraphNormCandidate (concreteL2GraphPairSub p q)

/-- Nonnegativity of the graph-norm distance candidate. -/
theorem concrete_l2_graph_norm_distance_candidate_nonneg
    (p q : ConcreteL2GraphPairSpace) :
    0 ≤ concreteL2GraphNormDistanceCandidate p q := by
  unfold concreteL2GraphNormDistanceCandidate
  exact concrete_l2_graph_norm_candidate_nonneg (concreteL2GraphPairSub p q)

/-- The graph-norm distance candidate vanishes on the diagonal. -/
theorem concrete_l2_graph_norm_distance_candidate_self
    (p : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormDistanceCandidate p p = 0 := by
  unfold concreteL2GraphNormDistanceCandidate
  rw [concrete_l2_graph_pair_sub_self p]
  exact concrete_l2_graph_norm_candidate_zero

/-- Package: explicit neg/sub API for graph-pair topology work. -/
def concreteL2MathlibSpectralAuditR2GraphPairNegSubAPI : Prop :=
  (∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphNormCandidate (concreteL2GraphPairNeg p) =
      concreteL2GraphNormCandidate p) ∧
  (∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphPairSub p p = concreteL2GraphPairZero)

/-- The explicit neg/sub API is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_pair_neg_sub_api :
    concreteL2MathlibSpectralAuditR2GraphPairNegSubAPI := by
  exact ⟨concrete_l2_graph_norm_candidate_neg, concrete_l2_graph_pair_sub_self⟩

/-- Package: graph-norm distance candidate basic laws. -/
def concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateBasicLaws : Prop :=
  (∀ p q : ConcreteL2GraphPairSpace,
    0 ≤ concreteL2GraphNormDistanceCandidate p q) ∧
  (∀ p : ConcreteL2GraphPairSpace,
    concreteL2GraphNormDistanceCandidate p p = 0)

/-- The graph-norm distance candidate basic laws are ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_basic_laws :
    concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateBasicLaws := by
  exact ⟨
    concrete_l2_graph_norm_distance_candidate_nonneg,
    concrete_l2_graph_norm_distance_candidate_self⟩

/-- Surface for graph-pair neg/sub and the graph-norm distance candidate. -/
structure ConcreteL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurface where
  distanceFrontierReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceFrontierSurfaceReady
  negSubAPI : concreteL2MathlibSpectralAuditR2GraphPairNegSubAPI
  distanceCandidate : ConcreteL2GraphPairSpace → ConcreteL2GraphPairSpace → ℝ
  distanceCandidate_eq : ∀ p q : ConcreteL2GraphPairSpace,
    distanceCandidate p q = concreteL2GraphNormCandidate (concreteL2GraphPairSub p q)
  distanceBasicLaws : concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateBasicLaws
  boundaryNotDistanceSymmetry : Prop
  boundaryNotDistanceTriangle : Prop
  boundaryNotPseudoMetricTopology : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete surface for graph-pair neg/sub and graph-norm distance candidate. -/
def concreteL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurface :
    ConcreteL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurface :=
  { distanceFrontierReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_distance_frontier_surface_ready
    negSubAPI :=
      concrete_l2_mathlib_spectral_audit_r2_graph_pair_neg_sub_api
    distanceCandidate := concreteL2GraphNormDistanceCandidate
    distanceCandidate_eq := fun _p _q => rfl
    distanceBasicLaws :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_basic_laws
    boundaryNotDistanceSymmetry := True
    boundaryNotDistanceTriangle := True
    boundaryNotPseudoMetricTopology := True
    boundaryNotDensity := True
    boundaryNotCore := True }

/-- Readiness predicate for the graph-pair neg/sub distance-candidate surface. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDistanceFrontierSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphPairNegSubAPI ∧
  concreteL2MathlibSpectralAuditR2GraphNormDistanceCandidateBasicLaws

/-- Readiness theorem for the graph-pair neg/sub distance-candidate surface. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_pair_neg_sub_distance_candidate_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphPairNegSubDistanceCandidateSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_distance_frontier_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_pair_neg_sub_api,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_distance_candidate_basic_laws⟩

end

end MathlibAnalytic
end MGAP4D
