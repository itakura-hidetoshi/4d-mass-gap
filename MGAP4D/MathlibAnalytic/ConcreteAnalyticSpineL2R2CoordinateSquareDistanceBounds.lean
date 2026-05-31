import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2CoordinateSquareDistanceLipschitzBridge
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphEnergyPrefixOrder

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- The first-coordinate square is bounded by the graph-pair energy term. -/
theorem concrete_l2_r2_graph_pair_fst_sq_le_energy_term
    (r : ConcreteL2GraphPairSpace) (n : ℕ) :
    (concreteL2GraphPairFst r).1 n ^ 2 ≤ concreteL2GraphPairEnergyTerm r n := by
  unfold concreteL2GraphPairEnergyTerm
  exact le_add_of_nonneg_right (sq_nonneg ((concreteL2GraphPairSnd r).1 n))

/-- The second-coordinate square is bounded by the graph-pair energy term. -/
theorem concrete_l2_r2_graph_pair_snd_sq_le_energy_term
    (r : ConcreteL2GraphPairSpace) (n : ℕ) :
    (concreteL2GraphPairSnd r).1 n ^ 2 ≤ concreteL2GraphPairEnergyTerm r n := by
  unfold concreteL2GraphPairEnergyTerm
  exact le_add_of_nonneg_left (sq_nonneg ((concreteL2GraphPairFst r).1 n))

/-- A single graph-pair energy term is bounded by the completed graph energy. -/
theorem concrete_l2_r2_graph_pair_energy_term_le_completed
    (r : ConcreteL2GraphPairSpace) (n : ℕ) :
    concreteL2GraphPairEnergyTerm r n ≤ concreteL2CompletedGraphEnergy r := by
  have h := concrete_l2_graph_energy_prefix_le_completed r ({n} : Finset ℕ)
  simpa using h

/-- The first-coordinate square is bounded by the completed graph energy. -/
theorem concrete_l2_r2_graph_pair_fst_sq_le_completed_energy
    (r : ConcreteL2GraphPairSpace) (n : ℕ) :
    (concreteL2GraphPairFst r).1 n ^ 2 ≤ concreteL2CompletedGraphEnergy r := by
  exact (concrete_l2_r2_graph_pair_fst_sq_le_energy_term r n).trans
    (concrete_l2_r2_graph_pair_energy_term_le_completed r n)

/-- The second-coordinate square is bounded by the completed graph energy. -/
theorem concrete_l2_r2_graph_pair_snd_sq_le_completed_energy
    (r : ConcreteL2GraphPairSpace) (n : ℕ) :
    (concreteL2GraphPairSnd r).1 n ^ 2 ≤ concreteL2CompletedGraphEnergy r := by
  exact (concrete_l2_r2_graph_pair_snd_sq_le_energy_term r n).trans
    (concrete_l2_r2_graph_pair_energy_term_le_completed r n)

/-- Real distance squared equals the coordinate difference squared. -/
theorem concrete_l2_r2_real_dist_sq_eq_sub_sq (a b : ℝ) :
    dist a b ^ 2 = (a - b) ^ 2 := by
  rw [Real.dist_eq]
  exact sq_abs (a - b)

/-- The first coordinate of the explicit graph-pair subtraction is the pointwise
first-coordinate difference. -/
theorem concrete_l2_r2_graph_pair_sub_fst_coordinate
    (q p : ConcreteL2GraphPairSpace) (n : ℕ) :
    (concreteL2GraphPairFst (concreteL2GraphPairSub q p)).1 n =
      q.1.1 n - p.1.1 n := by
  simp [concreteL2GraphPairSub, concreteL2GraphPairNeg, concreteL2GraphPairAdd,
    concreteL2GraphPairSmul, concreteL2RealAdd, concreteL2RealSmul,
    concreteL2GraphPairFst]

/-- The second coordinate of the explicit graph-pair subtraction is the pointwise
second-coordinate difference. -/
theorem concrete_l2_r2_graph_pair_sub_snd_coordinate
    (q p : ConcreteL2GraphPairSpace) (n : ℕ) :
    (concreteL2GraphPairSnd (concreteL2GraphPairSub q p)).1 n =
      q.2.1 n - p.2.1 n := by
  simp [concreteL2GraphPairSub, concreteL2GraphPairNeg, concreteL2GraphPairAdd,
    concreteL2GraphPairSmul, concreteL2RealAdd, concreteL2RealSmul,
    concreteL2GraphPairSnd]

/-- First-coordinate square-distance domination by completed graph energy. -/
theorem concrete_l2_r2_fst_coordinate_square_distance_bound
    (n : ℕ) :
    concreteL2R2GraphPairFstCoordinateSquareDistanceBound n := by
  unfold concreteL2R2GraphPairFstCoordinateSquareDistanceBound
  intro p q
  calc
    dist (q.1.1 n) (p.1.1 n) ^ 2 = (q.1.1 n - p.1.1 n) ^ 2 :=
      concrete_l2_r2_real_dist_sq_eq_sub_sq (q.1.1 n) (p.1.1 n)
    _ = (concreteL2GraphPairFst (concreteL2GraphPairSub q p)).1 n ^ 2 := by
      rw [concrete_l2_r2_graph_pair_sub_fst_coordinate q p n]
    _ ≤ concreteL2CompletedGraphEnergy (concreteL2GraphPairSub q p) :=
      concrete_l2_r2_graph_pair_fst_sq_le_completed_energy
        (concreteL2GraphPairSub q p) n

/-- Second-coordinate square-distance domination by completed graph energy. -/
theorem concrete_l2_r2_snd_coordinate_square_distance_bound
    (n : ℕ) :
    concreteL2R2GraphPairSndCoordinateSquareDistanceBound n := by
  unfold concreteL2R2GraphPairSndCoordinateSquareDistanceBound
  intro p q
  calc
    dist (q.2.1 n) (p.2.1 n) ^ 2 = (q.2.1 n - p.2.1 n) ^ 2 :=
      concrete_l2_r2_real_dist_sq_eq_sub_sq (q.2.1 n) (p.2.1 n)
    _ = (concreteL2GraphPairSnd (concreteL2GraphPairSub q p)).1 n ^ 2 := by
      rw [concrete_l2_r2_graph_pair_sub_snd_coordinate q p n]
    _ ≤ concreteL2CompletedGraphEnergy (concreteL2GraphPairSub q p) :=
      concrete_l2_r2_graph_pair_snd_sq_le_completed_energy
        (concreteL2GraphPairSub q p) n

/-- All coordinate square-distance domination bounds are proved. -/
theorem concrete_l2_r2_all_coordinate_square_distance_bounds :
    concreteL2R2AllCoordinateSquareDistanceBounds := by
  intro n
  exact ⟨
    concrete_l2_r2_snd_coordinate_square_distance_bound n,
    concrete_l2_r2_fst_coordinate_square_distance_bound n⟩

/-- The raw coordinate Lipschitz obligations are proved. -/
theorem concrete_l2_r2_all_coordinate_relation_lipschitz :
    concreteL2R2AllCoordinateRelationLipschitz := by
  exact concrete_l2_r2_all_coordinate_lipschitz_of_square_distance_bounds
    concrete_l2_r2_all_coordinate_square_distance_bounds

/-- The relation-map coordinate continuity obligations are proved. -/
theorem concrete_l2_r2_all_coordinate_relation_continuity :
    concreteL2R2AllCoordinateRelationContinuity := by
  exact concrete_l2_r2_all_coordinate_continuity_of_square_distance_bounds
    concrete_l2_r2_all_coordinate_square_distance_bounds

/-- The coordinate-limit obligation is proved from the explicit square-distance
bounds. -/
theorem concrete_l2_r2_closure_membership_to_coordinate_limit :
    concreteL2R2ClosureMembershipToCoordinateLimitObligation := by
  exact concrete_l2_r2_closure_membership_to_coordinate_limit_of_all_coordinate_lipschitz
    concrete_l2_r2_all_coordinate_relation_lipschitz

/-- The direct closed-graph witness is proved. -/
theorem concrete_l2_r2_direct_closed_graph_witness :
    concreteL2R2DirectClosedGraphWitness := by
  exact concrete_l2_r2_direct_closed_graph_witness_of_coordinate_limit
    concrete_l2_r2_closure_membership_to_coordinate_limit

/-- The original diagonal graph closedness theorem is proved. -/
theorem concrete_l2_r2_original_diagonal_graph_closed :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  exact concrete_l2_r2_original_diagonal_graph_closed_of_direct_witness
    concrete_l2_r2_direct_closed_graph_witness

/-- Readiness predicate for the completed coordinate square-distance bound layer. -/
def concreteAnalyticSpineL2R2CoordinateSquareDistanceBoundsReady : Prop :=
  concreteAnalyticSpineL2R2CoordinateSquareDistanceLipschitzBridgeReady ∧
  concreteL2R2AllCoordinateSquareDistanceBounds ∧
  concreteL2R2AllCoordinateRelationLipschitz ∧
  concreteL2R2AllCoordinateRelationContinuity ∧
  concreteL2R2ClosureMembershipToCoordinateLimitObligation ∧
  concreteL2R2DirectClosedGraphWitness ∧
  concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The completed coordinate square-distance bound layer is ready. -/
theorem concrete_analytic_spine_l2_r2_coordinate_square_distance_bounds_ready :
    concreteAnalyticSpineL2R2CoordinateSquareDistanceBoundsReady := by
  exact ⟨
    concrete_analytic_spine_l2_r2_coordinate_square_distance_lipschitz_bridge_ready,
    concrete_l2_r2_all_coordinate_square_distance_bounds,
    concrete_l2_r2_all_coordinate_relation_lipschitz,
    concrete_l2_r2_all_coordinate_relation_continuity,
    concrete_l2_r2_closure_membership_to_coordinate_limit,
    concrete_l2_r2_direct_closed_graph_witness,
    concrete_l2_r2_original_diagonal_graph_closed⟩

end

end MathlibAnalytic
end MGAP4D
