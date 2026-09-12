import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteFiniteDistance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- In the connected periodic plaquette graph, distance zero characterizes the
selected plaquette. -/
theorem periodicHypercubicPlaquetteDistance_eq_zero_iff
    (n : Nat) (hn : 2 ≤ n)
    (selected p : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteDistance n selected p = 0 ↔
      p = selected := by
  change (periodicHypercubicPlaquetteGraph n).dist selected p = 0 ↔ _
  simpa [eq_comm] using
    (periodicHypercubicPlaquetteGraph_connected n hn).dist_eq_zero_iff
      (u := selected) (v := p)

/-- A plaquette at distance `m + 1` admits an adjacent predecessor at distance
`m`, obtained from a shortest path. -/
theorem periodicHypercubicPlaquetteDistance_exists_predecessor
    (n : Nat) (hn : 2 ≤ n)
    (selected q : PeriodicHypercubicPlaquette n)
    (m : Nat)
    (hq : periodicHypercubicPlaquetteDistance n selected q = m + 1) :
    ∃ r : PeriodicHypercubicPlaquette n,
      periodicHypercubicPlaquetteDistance n selected r = m ∧
        periodicHypercubicPlaquetteAdjacent n r q := by
  let G := periodicHypercubicPlaquetteGraph n
  obtain ⟨w, _hwPath, hwLength⟩ :=
    (periodicHypercubicPlaquetteGraph_connected n hn selected q).exists_path_of_dist
  change G.dist selected q = m + 1 at hq
  have hLength : w.length = m + 1 := hwLength.trans hq
  let r := w.getVert m
  have hm_lt : m < w.length := by omega
  have hAdjRaw : G.Adj (w.getVert m) (w.getVert (m + 1)) := by
    exact w.adj_getVert_succ hm_lt
  have hEnd : w.getVert (m + 1) = q := by
    rw [← hLength]
    simp
  have hAdj : G.Adj r q := by
    exact hEnd ▸ hAdjRaw
  have hSubwalk :=
    SimpleGraph.length_eq_dist_of_subwalk hwLength (w.isSubwalk_take m)
  have hTakeLength : (w.take m).length = m := by
    simp [hLength]
  have hDistance : G.dist selected r = m := by
    rw [hTakeLength] at hSubwalk
    exact hSubwalk.symm
  refine ⟨r, ?_, ?_⟩
  · exact hDistance
  · exact hAdj

/-- The zero-distance shell is exactly the singleton selected plaquette. -/
theorem periodicHypercubicPlaquetteDistanceShell_zero
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (selected : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteDistanceShell n selected 0 = {selected} := by
  classical
  apply Finset.ext
  intro p
  simp [periodicHypercubicPlaquetteDistance_eq_zero_iff n hn selected p]

/-- Every plaquette in the next shell lies in the union of neighbor finsets of
the current shell. -/
theorem periodicHypercubicPlaquetteDistanceShell_succ_subset_neighbors
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (selected : PeriodicHypercubicPlaquette n)
    (m : Nat) :
    periodicHypercubicPlaquetteDistanceShell n selected (m + 1) ⊆
      (periodicHypercubicPlaquetteDistanceShell n selected m).biUnion
        (periodicHypercubicPlaquetteNeighbors n) := by
  classical
  intro q hq
  have hDistance :
      periodicHypercubicPlaquetteDistance n selected q = m + 1 :=
    (periodicHypercubic_mem_distanceShell_iff n selected q (m + 1)).mp hq
  obtain ⟨r, hrDistance, hrq⟩ :=
    periodicHypercubicPlaquetteDistance_exists_predecessor
      n hn selected q m hDistance
  apply Finset.mem_biUnion.mpr
  refine ⟨r, ?_, ?_⟩
  · exact (periodicHypercubic_mem_distanceShell_iff n selected r m).mpr hrDistance
  · exact (periodicHypercubic_mem_plaquetteNeighbors_iff n r q).mpr hrq

/-- One shell expansion multiplies cardinality by at most the uniform
plaquette-neighbor bound `24`. -/
theorem periodicHypercubicPlaquetteDistanceShell_succ_card_le
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (selected : PeriodicHypercubicPlaquette n)
    (m : Nat) :
    (periodicHypercubicPlaquetteDistanceShell n selected (m + 1)).card ≤
      (periodicHypercubicPlaquetteDistanceShell n selected m).card * 24 := by
  classical
  let shell := periodicHypercubicPlaquetteDistanceShell n selected m
  calc
    (periodicHypercubicPlaquetteDistanceShell n selected (m + 1)).card ≤
        (shell.biUnion (periodicHypercubicPlaquetteNeighbors n)).card :=
      Finset.card_le_card
        (periodicHypercubicPlaquetteDistanceShell_succ_subset_neighbors
          n hn selected m)
    _ ≤ ∑ p ∈ shell,
          (periodicHypercubicPlaquetteNeighbors n p).card :=
      finset_card_biUnion_le_sum_card shell
        (periodicHypercubicPlaquetteNeighbors n)
    _ ≤ ∑ _p ∈ shell, 24 := by
      apply Finset.sum_le_sum
      intro p _hp
      exact periodicHypercubicPlaquetteNeighbors_card_le_twenty_four n p
    _ = shell.card * 24 := by simp

/-- Distance-shell cardinalities grow at most exponentially with base `24`,
uniformly in the periodic side length and selected plaquette. -/
theorem periodicHypercubicPlaquetteDistanceShell_card_le_pow_twenty_four
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (selected : PeriodicHypercubicPlaquette n)
    (m : Nat) :
    (periodicHypercubicPlaquetteDistanceShell n selected m).card ≤ 24 ^ m := by
  induction m with
  | zero =>
      rw [periodicHypercubicPlaquetteDistanceShell_zero n hn selected]
      simp
  | succ m ih =>
      calc
        (periodicHypercubicPlaquetteDistanceShell n selected (m + 1)).card ≤
            (periodicHypercubicPlaquetteDistanceShell n selected m).card * 24 :=
          periodicHypercubicPlaquetteDistanceShell_succ_card_le
            n hn selected m
        _ ≤ 24 ^ m * 24 := Nat.mul_le_mul_right 24 ih
        _ = 24 ^ (m + 1) := by rw [pow_succ]

/-- Real-valued form of the explicit exponential shell bound, ready for the
exponential-shell covariance certificate. -/
theorem periodicHypercubicPlaquetteDistanceShell_card_real_le
    (n : Nat) [NeZero n] (hn : 2 ≤ n)
    (selected : PeriodicHypercubicPlaquette n)
    (m : Nat) :
    ((periodicHypercubicPlaquetteDistanceShell n selected m).card : Real) ≤
      (24 : Real) ^ m := by
  exact_mod_cast
    periodicHypercubicPlaquetteDistanceShell_card_le_pow_twenty_four
      n hn selected m

end

end MathlibAnalytic
end MGAP4D
