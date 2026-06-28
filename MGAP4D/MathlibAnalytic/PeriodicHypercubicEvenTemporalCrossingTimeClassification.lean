import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenFixedTimeClassification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingOpenHalfCharacterization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The canonical residue of one in the even periodic time circle is one. -/
@[simp]
theorem periodicHypercubicEven_one_val
    (H : ℕ) :
    (1 : ZMod (PeriodicHypercubicEvenSideLength H)).val = 1 := by
  have hone_lt : 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  simpa using (ZMod.val_natCast_of_lt hone_lt)

/-- Before the last residue, adding one does not wrap around the even periodic
time circle. -/
theorem periodicHypercubicEven_val_add_one_of_lt
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (h : t.val + 1 < PeriodicHypercubicEvenSideLength H) :
    (t + 1).val = t.val + 1 := by
  have hadd : t.val +
      (1 : ZMod (PeriodicHypercubicEvenSideLength H)).val <
        PeriodicHypercubicEvenSideLength H := by
    simpa using h
  simpa using
    (ZMod.val_add_of_lt
      (a := t)
      (b := (1 : ZMod (PeriodicHypercubicEvenSideLength H))) hadd)

/-- At the last residue, adding one wraps to zero. -/
theorem periodicHypercubicEven_val_add_one_of_not_lt
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (h : ¬ t.val + 1 < PeriodicHypercubicEvenSideLength H) :
    (t + 1).val = 0 := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  have htlt := ZMod.val_lt t
  have hsum : t.val + 1 = PeriodicHypercubicEvenSideLength H := by
    omega
  have hle : PeriodicHypercubicEvenSideLength H ≤
      t.val + (1 : ZMod (PeriodicHypercubicEvenSideLength H)).val := by
    simpa using hsum.ge
  calc
    (t + 1).val =
        t.val + (1 : ZMod (PeriodicHypercubicEvenSideLength H)).val -
          PeriodicHypercubicEvenSideLength H :=
      ZMod.val_add_of_le hle
    _ = 0 := by
      rw [periodicHypercubicEven_one_val H, hsum]
      exact Nat.sub_self _

/-- Two adjacent periodic times fail to lie wholly in either strict open half
exactly at the four boundary-adjacent base residues: `0`, `H`, `H+1`, and
`2H+1`. -/
theorem periodicHypercubicEven_adjacentTimes_not_sameOpenHalf_iff_val
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    (¬ (periodicHypercubicEvenStrictPositiveTime H t ∧
        periodicHypercubicEvenStrictPositiveTime H (t + 1)) ∧
      ¬ (periodicHypercubicEvenStrictNegativeTime H t ∧
        periodicHypercubicEvenStrictNegativeTime H (t + 1))) ↔
      t.val = 0 ∨ t.val = H ∨ t.val = H + 1 ∨ t.val = 2 * H + 1 := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  rw [periodicHypercubicEvenStrictPositiveTime_iff_val H t]
  rw [periodicHypercubicEvenStrictPositiveTime_iff_val H (t + 1)]
  rw [periodicHypercubicEvenStrictNegativeTime_iff_val H t]
  rw [periodicHypercubicEvenStrictNegativeTime_iff_val H (t + 1)]
  by_cases hnowrap : t.val + 1 < PeriodicHypercubicEvenSideLength H
  · rw [periodicHypercubicEven_val_add_one_of_lt H t hnowrap]
    have htlt := ZMod.val_lt t
    simp only [PeriodicHypercubicEvenSideLength] at hnowrap htlt ⊢
    omega
  · rw [periodicHypercubicEven_val_add_one_of_not_lt H t hnowrap]
    have htlt := ZMod.val_lt t
    simp only [PeriodicHypercubicEvenSideLength] at hnowrap htlt ⊢
    omega

/-- A temporal crossing plaquette is precisely a time-space plaquette based on
one of the four time layers adjacent to the two reflection-fixed planes. -/
theorem periodicHypercubicEvenTemporalCrossingPlaquette_iff_baseTime_val
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenTemporalCrossingPlaquette p ↔
      periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        (p.1 0).val = 0 ∨
      periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        (p.1 0).val = H ∨
      periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        (p.1 0).val = H + 1 ∨
      periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        (p.1 0).val = 2 * H + 1 := by
  rw [periodicHypercubicEvenTemporalCrossingPlaquette_iff_adjacentTimes_not_sameOpenHalf]
  rw [periodicHypercubicEven_adjacentTimes_not_sameOpenHalf_iff_val]
  tauto

end

end MathlibAnalytic
end MGAP4D