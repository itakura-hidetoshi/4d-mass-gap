import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A time-containing plaquette lies wholly in the strict positive open half
exactly when its base time and the adjacent next time are both strictly
positive. -/
theorem periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenStrictPositivePlaquette p ↔
      periodicHypercubicEvenStrictPositiveTime H (p.1 0) ∧
        periodicHypercubicEvenStrictPositiveTime H (p.1 0 + 1) := by
  constructor
  · intro hp
    have hbase := hp p.1 (by
      simp [periodicHypercubicEvenPlaquetteVertices,
        periodicHypercubicEvenPlaquetteCorner00])
    have hnext := hp (periodicHypercubicEvenPlaquetteCorner10 p) (by
      simp [periodicHypercubicEvenPlaquetteVertices])
    change periodicHypercubicEvenStrictPositiveTime H (p.1 0) at hbase
    change periodicHypercubicEvenStrictPositiveTime H
      (periodicHypercubicEvenPlaquetteCorner10 p 0) at hnext
    rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
      p htime] at hnext
    exact ⟨hbase, hnext⟩
  · rintro ⟨hbase, hnext⟩
    intro v hv
    unfold periodicHypercubicEvenStrictPositiveVertex
    simp [periodicHypercubicEvenPlaquetteVertices] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simpa [periodicHypercubicEvenPlaquetteCorner00] using hbase
    · rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
        p htime]
      exact hnext
    · rw [periodicHypercubicEvenPlaquetteCorner11_time_of_hasTimeDirection
        p htime]
      exact hnext
    · rw [periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
        p htime]
      exact hbase

/-- A time-containing plaquette lies wholly in the strict negative open half
exactly when its base time and the adjacent next time are both strictly
negative. -/
theorem periodicHypercubicEvenStrictNegativePlaquette_iff_adjacentTimes_of_hasTimeDirection
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (htime : periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenStrictNegativePlaquette p ↔
      periodicHypercubicEvenStrictNegativeTime H (p.1 0) ∧
        periodicHypercubicEvenStrictNegativeTime H (p.1 0 + 1) := by
  constructor
  · intro hp
    have hbase := hp p.1 (by
      simp [periodicHypercubicEvenPlaquetteVertices,
        periodicHypercubicEvenPlaquetteCorner00])
    have hnext := hp (periodicHypercubicEvenPlaquetteCorner10 p) (by
      simp [periodicHypercubicEvenPlaquetteVertices])
    change periodicHypercubicEvenStrictNegativeTime H (p.1 0) at hbase
    change periodicHypercubicEvenStrictNegativeTime H
      (periodicHypercubicEvenPlaquetteCorner10 p 0) at hnext
    rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
      p htime] at hnext
    exact ⟨hbase, hnext⟩
  · rintro ⟨hbase, hnext⟩
    intro v hv
    unfold periodicHypercubicEvenStrictNegativeVertex
    simp [periodicHypercubicEvenPlaquetteVertices] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simpa [periodicHypercubicEvenPlaquetteCorner00] using hbase
    · rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
        p htime]
      exact hnext
    · rw [periodicHypercubicEvenPlaquetteCorner11_time_of_hasTimeDirection
        p htime]
      exact hnext
    · rw [periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
        p htime]
      exact hbase

/-- Temporal crossing is exactly the condition that the two adjacent time
slices are neither both strictly positive nor both strictly negative. -/
theorem periodicHypercubicEvenTemporalCrossingPlaquette_iff_adjacentTimes_not_sameOpenHalf
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenTemporalCrossingPlaquette p ↔
      periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        ¬ (periodicHypercubicEvenStrictPositiveTime H (p.1 0) ∧
          periodicHypercubicEvenStrictPositiveTime H (p.1 0 + 1)) ∧
        ¬ (periodicHypercubicEvenStrictNegativeTime H (p.1 0) ∧
          periodicHypercubicEvenStrictNegativeTime H (p.1 0 + 1)) := by
  constructor
  · intro hp
    have htime := hp.2
    exact ⟨htime,
      fun hpos => hp.1.1
        ((periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
          p htime).2 hpos),
      fun hneg => hp.1.2
        ((periodicHypercubicEvenStrictNegativePlaquette_iff_adjacentTimes_of_hasTimeDirection
          p htime).2 hneg)⟩
  · rintro ⟨htime, hpos, hneg⟩
    exact ⟨⟨
      fun hp => hpos
        ((periodicHypercubicEvenStrictPositivePlaquette_iff_adjacentTimes_of_hasTimeDirection
          p htime).1 hp),
      fun hp => hneg
        ((periodicHypercubicEvenStrictNegativePlaquette_iff_adjacentTimes_of_hasTimeDirection
          p htime).1 hp)⟩,
      htime⟩

end

end MathlibAnalytic
end MGAP4D
