import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSixLinkOverlapV5_PZ37L
import Mathlib.Tactic

/-!
# PZ37L — exact 24-fold reduction for four actual odd-incidence edges

All temporal quadruples are retained until genuine centre parity excludes
them. If the actual odd support consists of four distinct links, the
surviving quadruples are exactly their 24 permutations.
-/
namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace PZ37OddFourPermutation
variable {α : Type*}
private def quadList (q : α × α × α × α) : List α := [q.1,q.2.1,q.2.2.1,q.2.2.2]
private theorem quadList_injective : Function.Injective (@quadList α) := by
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  simp only [quadList, List.cons.injEq, and_true] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl
private theorem four_of_perm {a b c d : α} {l : List α}
    (hp : l.Perm [a,b,c,d]) : ∃ e f g k : α, l = [e,f,g,k] := by
  have hlen : l.length = 4 := by simpa using hp.length_eq
  cases l with
  | nil => simp at hlen
  | cons e es =>
    cases es with
    | nil => simp at hlen
    | cons f fs =>
      cases fs with
      | nil => simp at hlen
      | cons g gs =>
        cases gs with
        | nil => simp at hlen
        | cons k ks =>
          cases ks with
          | nil => exact ⟨e,f,g,k,rfl⟩
          | cons z zs => simp at hlen

/-- Mathlib's permutation enumeration gives 24, without native evaluation. -/
theorem sum_permutations_four [Fintype α] [DecidableEq α]
    (a b c d : α) (hn : ([a,b,c,d] : List α).Nodup)
    (z : ℝ) :
    (∑ e : α, ∑ f : α, ∑ g : α, ∑ k : α,
      if ([e,f,g,k] : List α).Perm [a,b,c,d] then z else 0) = 24*z := by
  classical
  let s : Finset (α × α × α × α) := Finset.univ.filter
    (fun t => (quadList t).Perm [a,b,c,d])
  have hImage : s.image quadList = ([a,b,c,d] : List α).permutations.toFinset := by
    ext l
    constructor
    · intro hl
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hl
      have hp : (quadList t).Perm [a,b,c,d] := (Finset.mem_filter.mp ht).2
      simpa only [List.mem_toFinset, List.mem_permutations] using hp
    · intro hl
      have hp : l.Perm [a,b,c,d] := by
        simpa only [List.mem_toFinset, List.mem_permutations] using hl
      obtain ⟨e,f,g,k,rfl⟩ := four_of_perm hp
      refine Finset.mem_image.mpr ⟨(e,f,g,k), ?_, rfl⟩
      simpa [s, quadList] using hp
  have hCard : s.card = 24 := by
    calc
      s.card = (s.image quadList).card := (Finset.card_image_of_injective s quadList_injective).symm
      _ = ([a,b,c,d] : List α).permutations.toFinset.card := by rw [hImage]
      _ = ([a,b,c,d] : List α).permutations.length :=
        List.toFinset_card_of_nodup (List.nodup_permutations _ hn)
      _ = 24 := by rw [List.length_permutations]; norm_num
  have hSum : (∑ e : α, ∑ f : α, ∑ g : α, ∑ k : α,
      if ([e,f,g,k] : List α).Perm [a,b,c,d] then z else 0) = ∑ _t ∈ s, z := by
    simp only [s, Finset.sum_filter, Fintype.sum_prod_type, quadList]
  rw [hSum]
  simp [hCard, nsmul_eq_mul]
end PZ37OddFourPermutation

local instance (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _
namespace GroundStatePosteriorJoint
section OddFour
variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Plaq" => PeriodicHypercubicEvenSpatialSlicePlaquette H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Odd" => p4Q2PZ37I_originalPairOddEdge H
local notation "Covers" => p4Q2PZ37I_originalQuadCoversOddPair H
local notation "Term4" => p4Q2PZ37I_originalPairFourthTerm H
local notation "Pair4" => p4Q2PZ37I_originalPairTraceFourth H
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

/-- Exact four-odd-edge coverage is precisely a permutation, including repeats. -/
theorem p4Q2PZ37L_originalOddFour_cover_iff_perm
    (p q : Plaq) (a b c d : Link) (hn : ([a,b,c,d] : List Link).Nodup)
    (hOdd : ∀ x : Link, Odd p q x ↔ x ∈ [a,b,c,d]) (e f g k : Link) :
    Covers p q e f g k ↔ ([e,f,g,k] : List Link).Perm [a,b,c,d] := by
  classical
  have hBase : ([a,b,c,d] : List Link).toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hn]
    rfl
  constructor
  · intro hCover
    have hSub : ([a,b,c,d] : List Link).toFinset ⊆ ([e,f,g,k] : List Link).toFinset := by
      intro x hx
      have hxOdd := (hOdd x).mpr (List.mem_toFinset.mp hx)
      simpa using hCover x hxOdd
    have hEq : ([a,b,c,d] : List Link).toFinset = ([e,f,g,k] : List Link).toFinset := by
      apply Finset.eq_of_subset_of_card_le hSub
      rw [hBase]
      simpa using (List.toFinset_card_le ([e,f,g,k] : List Link))
    have hTuple : ([e,f,g,k] : List Link).Nodup := by
      have hFin : ([e,f,g,k] : List Link).toFinset.card = 4 := by rw [← hEq, hBase]
      have hCard :
          ((↑([e,f,g,k] : List Link) : Multiset Link).toFinset).card =
            (↑([e,f,g,k] : List Link) : Multiset Link).card := by
        simpa using hFin
      exact Multiset.coe_nodup.mp (Multiset.toFinset_card_eq_card_iff_nodup.mp hCard)
    exact List.perm_of_nodup_nodup_toFinset_eq hTuple hn hEq.symm
  · intro hp x hx
    have hm : x ∈ ([e,f,g,k] : List Link) := hp.mem_iff.mpr ((hOdd x).mp hx)
    simpa using hm

/-- Permuting the real Wilson-energy factors preserves the actual Haar term. -/
theorem p4Q2PZ37L_originalPairFourthTerm_perm
    (p q : Plaq) (a b c d e f g k : Link) (B : Cfg)
    (hp : ([e,f,g,k] : List Link).Perm [a,b,c,d]) :
    Term4 p q e f g k B = Term4 p q a b c d B := by
  unfold p4Q2PZ37I_originalPairFourthTerm
  apply integral_congr_ae
  filter_upwards with X
  have h := (hp.map (fun t => E ((X t)⁻¹*B t))).prod_eq
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  simp only [mul_assoc] at h ⊢
  rw [h]

/-- Actual pair response is exactly 24 copies of its four-odd-edge amplitude. -/
theorem p4Q2PZ37L_originalPairFourth_eq_twentyFour
    (p q : Plaq) (a b c d : Link) (hn : ([a,b,c,d] : List Link).Nodup)
    (hOdd : ∀ x : Link, Odd p q x ↔ x ∈ [a,b,c,d]) (B : Cfg) :
    Pair4 p q B = 24*Term4 p q a b c d B := by
  classical
  rw [p4Q2PZ37I_originalPairFourth_onlyOddCovered]
  unfold p4Q2PZ37I_originalPairFourth_oddSelected
  calc
    _ = ∑ e : Link, ∑ f : Link, ∑ g : Link, ∑ k : Link,
        if ([e,f,g,k] : List Link).Perm [a,b,c,d] then Term4 p q a b c d B else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro k _
      rw [p4Q2PZ37L_originalOddFour_cover_iff_perm H p q a b c d hn hOdd]
      split_ifs with hp
      · exact p4Q2PZ37L_originalPairFourthTerm_perm H p q a b c d e f g k B hp
      · rfl
    _ = _ := PZ37OddFourPermutation.sum_permutations_four a b c d hn _

end OddFour
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.PZ37OddFourPermutation.sum_permutations_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalOddFour_cover_iff_perm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalPairFourthTerm_perm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37L_originalPairFourth_eq_twentyFour
