import MGAP4D.MathlibAnalytic.KolmogorovCompactCylinderSystem
import Mathlib.MeasureTheory.Measure.AddContent

namespace MGAP4D
namespace MathlibAnalytic

open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- A finite additive content that admits arbitrarily accurate inner
approximations by a compact system is continuous from above at the empty set. -/
theorem regular_addContent_tendsto_zero
    {α : Type*} {C R : Set (Set α)} {s : ℕ → Set α}
    (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hs : ∀ n, s n ∈ R) (hsAnti : Antitone s)
    (hsInter : (⋂ n, s n) = ∅)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (hreg : ∀ A, A ∈ R → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K, K ∈ C ∧ K ⊆ A ∧ m (A \ K) ≤ ε) :
    Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
  cases isEmpty_or_nonempty α with
  | inl hα =>
      simp [Set.eq_empty_of_isEmpty]
  | inr hα =>
      rw [ENNReal.tendsto_nhds_zero]
      intro ε hε
      obtain ⟨δ, hδpos, hδsum⟩ :=
        ENNReal.exists_pos_sum_of_countable hε.ne' ℕ
      have happ : ∀ n, ∃ K, K ∈ C ∧ K ⊆ s n ∧ m (s n \ K) ≤ δ n := by
        intro n
        exact hreg (s n) (hs n) (δ n) (mod_cast hδpos n)
      choose t htC hts hmt using happ
      have htInter : (⋂ n, t n) = ∅ :=
        Set.subset_eq_empty (Set.iInter_mono hts) hsInter
      let N := hC.support htC htInter
      have hfinite : ⋂ i ≤ N, t i = ∅ :=
        hC.iInter_eq_empty htC htInter
      rw [eventually_atTop]
      refine ⟨N, fun n hn => ?_⟩
      have hfinite' : ⋂ i ≤ n, t i = ∅ := by
        refine Set.subset_eq_empty ?_ hfinite
        exact Set.biInter_mono fun i hi =>
          Set.biInter_subset_of_mem (hi.trans hn)
      calc
        m (s n) = m (⋂ i ≤ n, s i) := by
          congr
          exact le_antisymm
            (le_iInf₂ fun i hi => hsAnti hi)
            (iInf₂_le (κ := fun i => i ≤ n) (f := fun i _ => s i) n le_rfl)
        _ = m ((⋂ i ≤ n, s i) \ (⋂ i ≤ n, t i)) := by
          simp [hfinite']
        _ ≤ m (⋃ i ≤ n, s i \ t i) := by
          apply addContent_mono hR.isSetSemiring
          · exact hR.diff_mem
              (hR.iInter_le_mem hs n)
              (hR.iInter_le_mem (fun i => hCR (htC i)) n)
          · exact hR.iUnion_le_mem
              (fun i => hR.diff_mem (hs i) (hCR (htC i))) n
          · rw [Set.diff_iInter]
            intro x hx
            rcases hx with ⟨hxs, hxt⟩
            simp only [Set.mem_iUnion]
            by_contra hnone
            push_neg at hnone
            apply hxt
            simp only [Set.mem_iInter]
            intro i
            by_cases hi : i ≤ n
            · exact not_not.mp fun hnot =>
                hnone i hi ⟨Set.biInter_subset_of_mem hi hxs, hnot⟩
            · simp [hi]
        _ = m (⋃ i ∈ Finset.range (n + 1), s i \ t i) := by
          simp only [Finset.mem_range_succ_iff]
        _ ≤ ∑ i ∈ Finset.range (n + 1), m (s i \ t i) :=
          addContent_biUnion_le hR
            (fun i _ => hR.diff_mem (hs i) (hCR (htC i)))
        _ ≤ ∑ i ∈ Finset.range (n + 1), (δ i : ℝ≥0∞) :=
          Finset.sum_le_sum (fun i _ => hmt i)
        _ ≤ ∑' i, (δ i : ℝ≥0∞) := ENNReal.sum_le_tsum _
        _ ≤ ε := hδsum.le

/-- Compact inner regularity upgrades finite additivity on a ring to countable
additivity on pairwise disjoint sequences. -/
theorem regular_addContent_iUnion_eq_tsum
    {α : Type*} {C R : Set (Set α)}
    (hR : IsSetRing R) (m : AddContent ℝ≥0∞ R)
    (hmFinite : ∀ A ∈ R, m A ≠ ∞)
    (hC : IsCompactSystem C) (hCR : C ⊆ R)
    (hreg : ∀ A, A ∈ R → ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K, K ∈ C ∧ K ⊆ A ∧ m (A \ K) ≤ ε)
    {f : ℕ → Set α} (hf : ∀ n, f n ∈ R)
    (hUnion : (⋃ n, f n) ∈ R)
    (hdisjoint : Pairwise (Disjoint on f)) :
    m (⋃ n, f n) = ∑' n, m (f n) := by
  apply addContent_iUnion_eq_sum_of_tendsto_zero
    hR m hmFinite
  · intro s hs hsAnti hsInter
    exact regular_addContent_tendsto_zero
      hR m hs hsAnti hsInter hC hCR hreg
  · exact hf
  · exact hUnion
  · exact hdisjoint

end

end MathlibAnalytic
end MGAP4D
