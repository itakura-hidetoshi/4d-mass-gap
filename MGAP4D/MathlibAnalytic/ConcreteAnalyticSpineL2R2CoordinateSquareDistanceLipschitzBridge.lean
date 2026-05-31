import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateLipschitzContinuityBridge
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrder

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Real square-distance domination promotes to a square-root distance bound. -/
theorem concrete_l2_r2_real_dist_le_sqrt_of_sq_le
    {a b E : ℝ} (hE : 0 ≤ E) (hsq : dist a b ^ 2 ≤ E) :
    dist a b ≤ Real.sqrt E := by
  have hdist_nonneg : 0 ≤ dist a b := dist_nonneg
  have hsqrt_nonneg : 0 ≤ Real.sqrt E := Real.sqrt_nonneg E
  have hsq_sqrt : (Real.sqrt E) ^ 2 = E := by
    rw [Real.sq_sqrt hE]
  have hsq' : dist a b ^ 2 ≤ (Real.sqrt E) ^ 2 := by
    simpa [hsq_sqrt] using hsq
  have habs := (sq_le_sq.mp hsq')
  simpa [abs_of_nonneg hdist_nonneg, abs_of_nonneg hsqrt_nonneg] using habs

/-- Square-distance domination obligation for the first coordinate at `n`. -/
def concreteL2R2GraphPairFstCoordinateSquareDistanceBound (n : ℕ) : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    dist (q.1.1 n) (p.1.1 n) ^ 2 ≤
      concreteL2CompletedGraphEnergy (concreteL2GraphPairSub q p)

/-- Square-distance domination obligation for the second coordinate at `n`. -/
def concreteL2R2GraphPairSndCoordinateSquareDistanceBound (n : ℕ) : Prop :=
  ∀ p q : ConcreteL2GraphPairSpace,
    dist (q.2.1 n) (p.2.1 n) ^ 2 ≤
      concreteL2CompletedGraphEnergy (concreteL2GraphPairSub q p)

/-- All raw coordinate square-distance domination obligations. -/
def concreteL2R2AllCoordinateSquareDistanceBounds : Prop :=
  ∀ n : ℕ,
    concreteL2R2GraphPairSndCoordinateSquareDistanceBound n ∧
      concreteL2R2GraphPairFstCoordinateSquareDistanceBound n

/-- First-coordinate square-distance domination promotes to the first-coordinate
Lipschitz estimate. -/
theorem concrete_l2_r2_fst_coordinate_lipschitz_of_square_distance_bound
    (n : ℕ)
    (hbound : concreteL2R2GraphPairFstCoordinateSquareDistanceBound n) :
    concreteL2R2GraphPairFstCoordinateLipschitz n := by
  unfold concreteL2R2GraphPairFstCoordinateLipschitz
  unfold concreteL2R2GraphPairFstCoordinateSquareDistanceBound at hbound
  intro p q
  unfold concreteL2GraphNormDistanceCandidate concreteL2GraphNormCandidate
  exact concrete_l2_r2_real_dist_le_sqrt_of_sq_le
    (concrete_l2_completed_graph_energy_nonneg (concreteL2GraphPairSub q p))
    (hbound p q)

/-- Second-coordinate square-distance domination promotes to the second-coordinate
Lipschitz estimate. -/
theorem concrete_l2_r2_snd_coordinate_lipschitz_of_square_distance_bound
    (n : ℕ)
    (hbound : concreteL2R2GraphPairSndCoordinateSquareDistanceBound n) :
    concreteL2R2GraphPairSndCoordinateLipschitz n := by
  unfold concreteL2R2GraphPairSndCoordinateLipschitz
  unfold concreteL2R2GraphPairSndCoordinateSquareDistanceBound at hbound
  intro p q
  unfold concreteL2GraphNormDistanceCandidate concreteL2GraphNormCandidate
  exact concrete_l2_r2_real_dist_le_sqrt_of_sq_le
    (concrete_l2_completed_graph_energy_nonneg (concreteL2GraphPairSub q p))
    (hbound p q)

/-- All raw coordinate square-distance domination obligations promote to all raw
coordinate Lipschitz obligations. -/
theorem concrete_l2_r2_all_coordinate_lipschitz_of_square_distance_bounds
    (hbound : concreteL2R2AllCoordinateSquareDistanceBounds) :
    concreteL2R2AllCoordinateRelationLipschitz := by
  intro n
  exact ⟨
    concrete_l2_r2_snd_coordinate_lipschitz_of_square_distance_bound n (hbound n).1,
    concrete_l2_r2_fst_coordinate_lipschitz_of_square_distance_bound n (hbound n).2⟩

/-- All raw coordinate square-distance domination obligations promote to all
coordinate continuity obligations for the relation maps. -/
theorem concrete_l2_r2_all_coordinate_continuity_of_square_distance_bounds
    (hbound : concreteL2R2AllCoordinateSquareDistanceBounds) :
    concreteL2R2AllCoordinateRelationContinuity := by
  exact concrete_l2_r2_all_coordinate_continuity_of_all_coordinate_lipschitz
    (concrete_l2_r2_all_coordinate_lipschitz_of_square_distance_bounds hbound)

/-- All raw coordinate square-distance domination obligations promote to original
diagonal graph closedness. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_square_distance_bounds
    (hbound : concreteL2R2AllCoordinateSquareDistanceBounds) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_all_coordinate_lipschitz
    (concrete_l2_r2_all_coordinate_lipschitz_of_square_distance_bounds hbound)

/-- Promotion proposition from square-distance bounds to raw coordinate Lipschitz
estimates. -/
def concreteL2R2SquareDistanceBoundsToCoordinateLipschitzPromotion : Prop :=
  concreteL2R2AllCoordinateSquareDistanceBounds →
    concreteL2R2AllCoordinateRelationLipschitz

/-- The square-distance-bounds to coordinate-Lipschitz promotion is proved. -/
theorem concrete_l2_r2_square_distance_bounds_to_coordinate_lipschitz_promotion_ready :
    concreteL2R2SquareDistanceBoundsToCoordinateLipschitzPromotion := by
  intro hbound
  exact concrete_l2_r2_all_coordinate_lipschitz_of_square_distance_bounds hbound

/-- Promotion proposition from square-distance bounds to original graph closedness. -/
def concreteL2R2SquareDistanceBoundsToOriginalGraphClosedPromotion : Prop :=
  concreteL2R2AllCoordinateSquareDistanceBounds →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The square-distance-bounds to original-graph-closedness promotion is proved. -/
theorem concrete_l2_r2_square_distance_bounds_to_original_graph_closed_promotion_ready :
    concreteL2R2SquareDistanceBoundsToOriginalGraphClosedPromotion := by
  intro hbound
  exact concrete_l2_r2_original_diagonal_graph_closed_of_square_distance_bounds hbound

/-- Readiness predicate for the square-distance to Lipschitz bridge. -/
def concreteAnalyticSpineL2R2CoordinateSquareDistanceLipschitzBridgeReady : Prop :=
  concreteAnalyticSpineL2R2CoordinateLipschitzContinuityBridgeReady ∧
  concreteL2R2SquareDistanceBoundsToCoordinateLipschitzPromotion ∧
  concreteL2R2SquareDistanceBoundsToOriginalGraphClosedPromotion

/-- The square-distance to Lipschitz bridge is ready. -/
theorem concrete_analytic_spine_l2_r2_coordinate_square_distance_lipschitz_bridge_ready :
    concreteAnalyticSpineL2R2CoordinateSquareDistanceLipschitzBridgeReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_coordinate_lipschitz_continuity_bridge_ready,
    concrete_l2_r2_square_distance_bounds_to_coordinate_lipschitz_promotion_ready,
    concrete_l2_r2_square_distance_bounds_to_original_graph_closed_promotion_ready⟩

end

end MathlibAnalytic
end MGAP4D
