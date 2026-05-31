import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateRelationClosedBridge
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPseudoMetricConstruction

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- Lipschitz-type obligation for the second-coordinate evaluation at coordinate
`n`, measured by the explicit graph-norm distance candidate. -/
def concreteL2R2GraphPairSndCoordinateLipschitz (n : ℕ) : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    dist (q.2.1 n) (p.2.1 n) ≤ concreteL2GraphNormDistanceCandidate q p

/-- Lipschitz-type obligation for the weighted first-coordinate evaluation at
coordinate `n`, measured by the explicit graph-norm distance candidate. -/
def concreteL2R2GraphPairWeightedFstCoordinateLipschitz (n : ℕ) : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    dist (concreteL2DiagonalWeight n * q.1.1 n)
      (concreteL2DiagonalWeight n * p.1.1 n) ≤
        concreteL2GraphNormDistanceCandidate q p

/-- All coordinate Lipschitz obligations for the two maps defining the diagonal
relation. -/
def concreteL2R2AllCoordinateRelationLipschitz : Prop :=
  ∀ n : ℕ,
    concreteL2R2GraphPairSndCoordinateLipschitz n ∧
      concreteL2R2GraphPairWeightedFstCoordinateLipschitz n

/-- A second-coordinate graph-norm Lipschitz estimate implies graph-norm
continuity of the second-coordinate evaluation. -/
theorem concrete_l2_r2_snd_coordinate_continuous_of_lipschitz
    (n : ℕ)
    (hLip : concreteL2R2GraphPairSndCoordinateLipschitz n) :
    concreteL2R2GraphPairSndCoordinateContinuous n := by
  unfold concreteL2R2GraphPairSndCoordinateContinuous
  unfold concreteL2R2GraphPairSndCoordinateLipschitz at hLip
  letI : PseudoMetricSpace ConcreteL2GraphPairSpace := concreteL2GraphNormPseudoMetricSpace
  change Continuous fun p : ConcreteL2GraphPairSpace => p.2.1 n
  rw [Metric.continuous_iff]
  intro p ε hε
  refine ⟨ε, hε, ?_⟩
  intro q hq
  calc
    dist ((fun r : ConcreteL2GraphPairSpace => r.2.1 n) q)
        ((fun r : ConcreteL2GraphPairSpace => r.2.1 n) p)
        ≤ concreteL2GraphNormDistanceCandidate q p := hLip p q
    _ = dist q p := by rfl
    _ < ε := hq

/-- A weighted first-coordinate graph-norm Lipschitz estimate implies graph-norm
continuity of the weighted first-coordinate evaluation. -/
theorem concrete_l2_r2_weighted_fst_coordinate_continuous_of_lipschitz
    (n : ℕ)
    (hLip : concreteL2R2GraphPairWeightedFstCoordinateLipschitz n) :
    concreteL2R2GraphPairWeightedFstCoordinateContinuous n := by
  unfold concreteL2R2GraphPairWeightedFstCoordinateContinuous
  unfold concreteL2R2GraphPairWeightedFstCoordinateLipschitz at hLip
  letI : PseudoMetricSpace ConcreteL2GraphPairSpace := concreteL2GraphNormPseudoMetricSpace
  change Continuous fun p : ConcreteL2GraphPairSpace =>
    concreteL2DiagonalWeight n * p.1.1 n
  rw [Metric.continuous_iff]
  intro p ε hε
  refine ⟨ε, hε, ?_⟩
  intro q hq
  calc
    dist ((fun r : ConcreteL2GraphPairSpace => concreteL2DiagonalWeight n * r.1.1 n) q)
        ((fun r : ConcreteL2GraphPairSpace => concreteL2DiagonalWeight n * r.1.1 n) p)
        ≤ concreteL2GraphNormDistanceCandidate q p := hLip p q
    _ = dist q p := by rfl
    _ < ε := hq

/-- All coordinate Lipschitz obligations imply all coordinate continuity
obligations. -/
theorem concrete_l2_r2_all_coordinate_continuity_of_all_coordinate_lipschitz
    (hLip : concreteL2R2AllCoordinateRelationLipschitz) :
    concreteL2R2AllCoordinateRelationContinuity := by
  intro n
  exact ⟨
    concrete_l2_r2_snd_coordinate_continuous_of_lipschitz n (hLip n).1,
    concrete_l2_r2_weighted_fst_coordinate_continuous_of_lipschitz n (hLip n).2⟩

/-- All coordinate Lipschitz obligations promote to coordinate relation set
closedness. -/
theorem concrete_l2_r2_coordinate_relation_sets_closed_of_all_coordinate_lipschitz
    (hLip : concreteL2R2AllCoordinateRelationLipschitz) :
    ∀ n : ℕ, concreteL2R2CoordinateRelationSetClosed n := by
  exact concrete_l2_r2_coordinate_relation_sets_closed_of_all_coordinate_continuity
    (concrete_l2_r2_all_coordinate_continuity_of_all_coordinate_lipschitz hLip)

/-- All coordinate Lipschitz obligations promote to the coordinate-limit
obligation. -/
theorem concrete_l2_r2_closure_membership_to_coordinate_limit_of_all_coordinate_lipschitz
    (hLip : concreteL2R2AllCoordinateRelationLipschitz) :
    concreteL2R2ClosureMembershipToCoordinateLimitObligation := by
  exact concrete_l2_r2_closure_membership_to_coordinate_limit_of_all_coordinate_continuity
    (concrete_l2_r2_all_coordinate_continuity_of_all_coordinate_lipschitz hLip)

/-- All coordinate Lipschitz obligations promote to original diagonal graph
closedness. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_all_coordinate_lipschitz
    (hLip : concreteL2R2AllCoordinateRelationLipschitz) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_all_coordinate_continuity
    (concrete_l2_r2_all_coordinate_continuity_of_all_coordinate_lipschitz hLip)

/-- Promotion proposition from all coordinate Lipschitz obligations to all
coordinate continuity obligations. -/
def concreteL2R2AllCoordinateLipschitzToContinuityPromotion : Prop :=
  concreteL2R2AllCoordinateRelationLipschitz →
    concreteL2R2AllCoordinateRelationContinuity

/-- The all-coordinate-Lipschitz to all-coordinate-continuity promotion is proved. -/
theorem concrete_l2_r2_all_coordinate_lipschitz_to_continuity_promotion_ready :
    concreteL2R2AllCoordinateLipschitzToContinuityPromotion := by
  intro hLip
  exact concrete_l2_r2_all_coordinate_continuity_of_all_coordinate_lipschitz hLip

/-- Promotion proposition from all coordinate Lipschitz obligations to original
diagonal graph closedness. -/
def concreteL2R2AllCoordinateLipschitzToOriginalGraphClosedPromotion : Prop :=
  concreteL2R2AllCoordinateRelationLipschitz →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The all-coordinate-Lipschitz to original-graph-closedness promotion is proved. -/
theorem concrete_l2_r2_all_coordinate_lipschitz_to_original_graph_closed_promotion_ready :
    concreteL2R2AllCoordinateLipschitzToOriginalGraphClosedPromotion := by
  intro hLip
  exact concrete_l2_r2_original_diagonal_graph_closed_of_all_coordinate_lipschitz hLip

/-- Readiness predicate for the coordinate Lipschitz-to-continuity bridge. -/
def concreteAnalyticSpineL2R2CoordinateLipschitzContinuityBridgeReady : Prop :=
  concreteAnalyticSpineL2R2CoordinateRelationClosedBridgeReady ∧
  concreteL2R2AllCoordinateLipschitzToContinuityPromotion ∧
  concreteL2R2AllCoordinateLipschitzToOriginalGraphClosedPromotion

/-- The coordinate Lipschitz-to-continuity bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_coordinate_lipschitz_continuity_bridge_ready :
    concreteAnalyticSpineL2R2CoordinateLipschitzContinuityBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_coordinate_relation_closed_bridge_ready,
    concrete_l2_r2_all_coordinate_lipschitz_to_continuity_promotion_ready,
    concrete_l2_r2_all_coordinate_lipschitz_to_original_graph_closed_promotion_ready⟩

end

end MathlibAnalytic
end MGAP4D
