import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCrossingWilsonActionSpatialTemporal

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- If a plaquette has no Euclidean-time direction, its first coordinate axis is
spatial. -/
theorem periodicHypercubicEvenPlaquetteFirstAxis_ne_zero_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteFirstAxis p ≠ 0 := by
  intro h
  exact htime (Or.inl h)

/-- If a plaquette has no Euclidean-time direction, its second coordinate axis
is spatial. -/
theorem periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicPlaquetteSecondAxis p ≠ 0 := by
  intro h
  exact htime (Or.inr h)

/-- The first shifted corner of a purely spatial plaquette has the same time
coordinate as its base. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteCorner10_time_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenPlaquetteCorner10 p 0 = p.1 0 := by
  have haxis : (0 : PeriodicHypercubicAxis) ≠
      periodicHypercubicPlaquetteFirstAxis p :=
    Ne.symm
      (periodicHypercubicEvenPlaquetteFirstAxis_ne_zero_of_not_hasTimeDirection
        p htime)
  simp [periodicHypercubicEvenPlaquetteCorner10,
    periodicHypercubicShift_apply, haxis]

/-- The second shifted corner of a purely spatial plaquette has the same time
coordinate as its base. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteCorner01_time_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenPlaquetteCorner01 p 0 = p.1 0 := by
  have haxis : (0 : PeriodicHypercubicAxis) ≠
      periodicHypercubicPlaquetteSecondAxis p :=
    Ne.symm
      (periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_not_hasTimeDirection
        p htime)
  simp [periodicHypercubicEvenPlaquetteCorner01,
    periodicHypercubicShift_apply, haxis]

/-- The doubly shifted corner of a purely spatial plaquette has the same time
coordinate as its base. -/
@[simp]
theorem periodicHypercubicEvenPlaquetteCorner11_time_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenPlaquetteCorner11 p 0 = p.1 0 := by
  have haxis : (0 : PeriodicHypercubicAxis) ≠
      periodicHypercubicPlaquetteSecondAxis p :=
    Ne.symm
      (periodicHypercubicEvenPlaquetteSecondAxis_ne_zero_of_not_hasTimeDirection
        p htime)
  simp [periodicHypercubicEvenPlaquetteCorner11,
    periodicHypercubicShift_apply, haxis,
    periodicHypercubicEvenPlaquetteCorner10_time_of_not_hasTimeDirection p htime]

/-- A purely spatial plaquette lies in the strict positive open half exactly
when its base vertex does. -/
theorem periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenStrictPositivePlaquette p ↔
      periodicHypercubicEvenStrictPositiveVertex H p.1 := by
  constructor
  · intro hp
    exact hp p.1 (by
      simp [periodicHypercubicEvenPlaquetteVertices,
        periodicHypercubicEvenPlaquetteCorner00])
  · intro hb v hv
    simp [periodicHypercubicEvenPlaquetteVertices] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simpa [periodicHypercubicEvenPlaquetteCorner00] using hb
    · simpa [periodicHypercubicEvenStrictPositiveVertex,
        periodicHypercubicEvenPlaquetteCorner10_time_of_not_hasTimeDirection
          p htime] using hb
    · simpa [periodicHypercubicEvenStrictPositiveVertex,
        periodicHypercubicEvenPlaquetteCorner11_time_of_not_hasTimeDirection
          p htime] using hb
    · simpa [periodicHypercubicEvenStrictPositiveVertex,
        periodicHypercubicEvenPlaquetteCorner01_time_of_not_hasTimeDirection
          p htime] using hb

/-- A purely spatial plaquette lies in the strict negative open half exactly
when its base vertex does. -/
theorem periodicHypercubicEvenStrictNegativePlaquette_iff_base_of_not_hasTimeDirection
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H)
    (htime : ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) :
    periodicHypercubicEvenStrictNegativePlaquette p ↔
      periodicHypercubicEvenStrictNegativeVertex H p.1 := by
  constructor
  · intro hp
    exact hp p.1 (by
      simp [periodicHypercubicEvenPlaquetteVertices,
        periodicHypercubicEvenPlaquetteCorner00])
  · intro hb v hv
    simp [periodicHypercubicEvenPlaquetteVertices] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simpa [periodicHypercubicEvenPlaquetteCorner00] using hb
    · simpa [periodicHypercubicEvenStrictNegativeVertex,
        periodicHypercubicEvenPlaquetteCorner10_time_of_not_hasTimeDirection
          p htime] using hb
    · simpa [periodicHypercubicEvenStrictNegativeVertex,
        periodicHypercubicEvenPlaquetteCorner11_time_of_not_hasTimeDirection
          p htime] using hb
    · simpa [periodicHypercubicEvenStrictNegativeVertex,
        periodicHypercubicEvenPlaquetteCorner01_time_of_not_hasTimeDirection
          p htime] using hb

/-- A spatial crossing plaquette is precisely a plaquette with no time direction
whose base vertex belongs to neither strict open half. -/
theorem periodicHypercubicEvenSpatialCrossingPlaquette_iff_base_not_openHalf
    {H : ℕ} (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenSpatialCrossingPlaquette p ↔
      ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        ¬ periodicHypercubicEvenStrictPositiveVertex H p.1 ∧
        ¬ periodicHypercubicEvenStrictNegativeVertex H p.1 := by
  change
    ((¬ periodicHypercubicEvenStrictPositivePlaquette p ∧
        ¬ periodicHypercubicEvenStrictNegativePlaquette p) ∧
      ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p) ↔
      ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        ¬ periodicHypercubicEvenStrictPositiveVertex H p.1 ∧
        ¬ periodicHypercubicEvenStrictNegativeVertex H p.1
  constructor
  · rintro ⟨⟨hpos, hneg⟩, htime⟩
    exact ⟨htime,
      fun hb => hpos
        ((periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
          p htime).2 hb),
      fun hb => hneg
        ((periodicHypercubicEvenStrictNegativePlaquette_iff_base_of_not_hasTimeDirection
          p htime).2 hb)⟩
  · rintro ⟨htime, hpos, hneg⟩
    exact ⟨⟨
      fun hp => hpos
        ((periodicHypercubicEvenStrictPositivePlaquette_iff_base_of_not_hasTimeDirection
          p htime).1 hp),
      fun hp => hneg
        ((periodicHypercubicEvenStrictNegativePlaquette_iff_base_of_not_hasTimeDirection
          p htime).1 hp)⟩,
      htime⟩

end

end MathlibAnalytic
end MGAP4D
