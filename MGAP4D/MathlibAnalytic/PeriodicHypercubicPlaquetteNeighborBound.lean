import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteAdjacency
import MGAP4D.MathlibAnalytic.PeriodicHypercubicActiveNeighborBound
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- All periodic hypercubic plaquettes sharing a physical boundary link with a
selected plaquette, with the selected plaquette itself removed. -/
noncomputable def periodicHypercubicPlaquetteNeighbors
    (n : Nat) [NeZero n]
    (p : PeriodicHypercubicPlaquette n) :
    Finset (PeriodicHypercubicPlaquette n) := by
  classical
  exact (periodicHypercubicPlaquetteEdges n p).biUnion fun e =>
    (periodicHypercubicTouchingPlaquettes n e).erase p

/-- Membership in the explicit neighbor finset is equivalent to shared-link
plaquette adjacency. -/
theorem periodicHypercubic_mem_plaquetteNeighbors_iff
    (n : Nat) [NeZero n]
    (p q : PeriodicHypercubicPlaquette n) :
    q ∈ periodicHypercubicPlaquetteNeighbors n p ↔
      periodicHypercubicPlaquetteAdjacent n p q := by
  classical
  constructor
  · intro hq
    unfold periodicHypercubicPlaquetteNeighbors at hq
    rcases Finset.mem_biUnion.mp hq with ⟨e, he, hqErase⟩
    have hqData := Finset.mem_erase.mp hqErase
    apply periodicHypercubicPlaquetteAdjacent_of_shared_edge n
    · exact Ne.symm hqData.1
    · exact e
    · unfold periodicHypercubicPlaquetteEdges at he
      rcases Finset.mem_image.mp he with ⟨k, _hk, hk⟩
      exact ⟨k, hk⟩
    · exact (periodicHypercubic_mem_touchingPlaquettes_iff n e q).mp hqData.2
  · intro h
    rcases h with ⟨hpq, e, hp, hq⟩
    unfold periodicHypercubicPlaquetteNeighbors
    apply Finset.mem_biUnion.mpr
    refine ⟨e, periodicHypercubic_mem_plaquetteEdges_of_touches n p e hp, ?_⟩
    apply Finset.mem_erase.mpr
    exact ⟨Ne.symm hpq,
      (periodicHypercubic_mem_touchingPlaquettes_iff n e q).mpr hq⟩

/-- A periodic four-dimensional plaquette has at most 24 shared-link
plaquette neighbors, independently of the side length. -/
theorem periodicHypercubicPlaquetteNeighbors_card_le_twenty_four
    (n : Nat) [NeZero n]
    (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicPlaquetteNeighbors n p).card ≤ 24 := by
  classical
  calc
    (periodicHypercubicPlaquetteNeighbors n p).card ≤
        ∑ e ∈ periodicHypercubicPlaquetteEdges n p,
          ((periodicHypercubicTouchingPlaquettes n e).erase p).card := by
      unfold periodicHypercubicPlaquetteNeighbors
      exact finset_card_biUnion_le_sum_card
        (periodicHypercubicPlaquetteEdges n p)
        (fun e => (periodicHypercubicTouchingPlaquettes n e).erase p)
    _ ≤ ∑ _e ∈ periodicHypercubicPlaquetteEdges n p, 6 := by
      apply Finset.sum_le_sum
      intro e _he
      exact
        (Finset.card_le_card
          (Finset.erase_subset p
            (periodicHypercubicTouchingPlaquettes n e))).trans
          (periodicHypercubicTouchingPlaquettes_card_le_six n e)
    _ = (periodicHypercubicPlaquetteEdges n p).card * 6 := by simp
    _ ≤ 4 * 6 := Nat.mul_le_mul_right 6
      (periodicHypercubicPlaquetteEdges_card_le_four n p)
    _ = 24 := by norm_num

end

end MathlibAnalytic
end MGAP4D
