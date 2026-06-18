import MGAP4D.MathlibAnalytic.PeriodicHypercubicPlaquetteIncidenceCompleteness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped BigOperators

/-- Cardinality of a finite union is bounded by the sum of the cardinalities.
This local lemma keeps the active-neighbor count on elementary `Finset`
principles. -/
theorem finset_card_biUnion_le_sum_card
    {α β : Type} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → Finset β) :
    (s.biUnion f).card ≤ ∑ a in s, (f a).card := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.biUnion_insert]
      calc
        (f a ∪ s.biUnion f).card ≤
            (f a).card + (s.biUnion f).card :=
          Finset.card_union_le
        _ ≤ (f a).card + ∑ b in s, (f b).card :=
          Nat.add_le_add_left ih _
        _ = ∑ b in insert a s, (f b).card := by
          simp [ha]

/-- The physical boundary-link set of one signed plaquette. -/
noncomputable def periodicHypercubicPlaquetteEdges
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    Finset (PeriodicHypercubicEdge n) := by
  classical
  exact Finset.univ.image fun k : Fin 4 =>
    periodicHypercubicPhysicalBoundaryEdge n p k

/-- A plaquette has at most four physical boundary links. -/
theorem periodicHypercubicPlaquetteEdges_card_le_four
    (n : ℕ) (p : PeriodicHypercubicPlaquette n) :
    (periodicHypercubicPlaquetteEdges n p).card ≤ 4 := by
  classical
  unfold periodicHypercubicPlaquetteEdges
  calc
    (Finset.univ.image fun k : Fin 4 =>
      periodicHypercubicPhysicalBoundaryEdge n p k).card ≤
        (Finset.univ : Finset (Fin 4)).card :=
      Finset.card_image_le
    _ = 4 := by simp

/-- A touching witness puts the target link in the physical boundary set. -/
theorem periodicHypercubic_mem_plaquetteEdges_of_touches
    (n : ℕ)
    (p : PeriodicHypercubicPlaquette n)
    (target : PeriodicHypercubicEdge n)
    (hTouches : periodicHypercubicPlaquetteTouchesEdge n p target) :
    target ∈ periodicHypercubicPlaquetteEdges n p := by
  classical
  rcases hTouches with ⟨k, hk⟩
  unfold periodicHypercubicPlaquetteEdges
  apply Finset.mem_image.mpr
  exact ⟨k, Finset.mem_univ _, hk⟩

/-- Other physical links of a plaquette, with the target erased. -/
noncomputable def periodicHypercubicPlaquetteOtherEdges
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (p : PeriodicHypercubicPlaquette n) :
    Finset (PeriodicHypercubicEdge n) := by
  classical
  exact (periodicHypercubicPlaquetteEdges n p).erase target

/-- Once a touching target is erased, at most three boundary links remain. -/
theorem periodicHypercubicPlaquetteOtherEdges_card_le_three
    (n : ℕ)
    (target : PeriodicHypercubicEdge n)
    (p : PeriodicHypercubicPlaquette n)
    (hTouches : periodicHypercubicPlaquetteTouchesEdge n p target) :
    (periodicHypercubicPlaquetteOtherEdges n target p).card ≤ 3 := by
  classical
  have hmem : target ∈ periodicHypercubicPlaquetteEdges n p :=
    periodicHypercubic_mem_plaquetteEdges_of_touches n p target hTouches
  have hfour : (periodicHypercubicPlaquetteEdges n p).card ≤ 4 :=
    periodicHypercubicPlaquetteEdges_card_le_four n p
  unfold periodicHypercubicPlaquetteOtherEdges
  rw [Finset.card_erase_of_mem hmem]
  omega

/-- Physical active neighbors of a target link: all other physical links in a
plaquette touching the target. -/
noncomputable def periodicHypercubicActiveNeighbors
    (n : ℕ) [NeZero n]
    (target : PeriodicHypercubicEdge n) :
    Finset (PeriodicHypercubicEdge n) := by
  classical
  exact (periodicHypercubicTouchingPlaquettes n target).biUnion fun p =>
    periodicHypercubicPlaquetteOtherEdges n target p

/-- The four-dimensional periodic hypercubic active-neighbor degree is bounded
by `6 * 3 = 18`, independently of the volume. -/
theorem periodicHypercubicActiveNeighbors_card_le_eighteen
    (n : ℕ) [NeZero n]
    (target : PeriodicHypercubicEdge n) :
    (periodicHypercubicActiveNeighbors n target).card ≤ 18 := by
  classical
  let touching := periodicHypercubicTouchingPlaquettes n target
  calc
    (periodicHypercubicActiveNeighbors n target).card ≤
        ∑ p in touching,
          (periodicHypercubicPlaquetteOtherEdges n target p).card := by
      unfold periodicHypercubicActiveNeighbors
      exact finset_card_biUnion_le_sum_card touching
        (periodicHypercubicPlaquetteOtherEdges n target)
    _ ≤ ∑ _p in touching, 3 := by
      apply Finset.sum_le_sum
      intro p hp
      apply periodicHypercubicPlaquetteOtherEdges_card_le_three n target p
      exact (periodicHypercubic_mem_touchingPlaquettes_iff n target p).mp hp
    _ = touching.card * 3 := by simp
    _ ≤ 6 * 3 := Nat.mul_le_mul_right 3
      (periodicHypercubicTouchingPlaquettes_card_le_six n target)
    _ = 18 := by norm_num

end

end MathlibAnalytic
end MGAP4D
