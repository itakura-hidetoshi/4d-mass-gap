import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialCrossingGeometry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A periodic time belongs to the strict positive open half exactly when its
canonical residue lies in the interval `1, ..., H`. -/
theorem periodicHypercubicEvenStrictPositiveTime_iff_val
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenStrictPositiveTime H t ↔
      1 ≤ t.val ∧ t.val ≤ H := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  constructor
  · rintro ⟨k, rfl⟩
    have hklt : k.1 + 1 < PeriodicHypercubicEvenSideLength H := by
      have hk : k.1 < H := k.2
      simp only [PeriodicHypercubicEvenSideLength]
      omega
    rw [ZMod.val_natCast_of_lt hklt]
    exact ⟨by omega, by omega⟩
  · rintro ⟨hpos, hle⟩
    let k : Fin H := ⟨t.val - 1, by omega⟩
    refine ⟨k, ?_⟩
    rw [← ZMod.natCast_zmod_val t]
    have hval : t.val = k.1 + 1 := by
      dsimp [k]
      omega
    exact congrArg
      (fun a : ℕ => (a : ZMod (PeriodicHypercubicEvenSideLength H))) hval

/-- Away from zero, negation replaces the canonical residue `r` by
`2(H+1)-r`. -/
theorem periodicHypercubicEven_neg_val_of_ne_zero
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H))
    (ht : t ≠ 0) :
    (-t).val = PeriodicHypercubicEvenSideLength H - t.val := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  have htval_pos : 0 < t.val := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact ht ((ZMod.val_eq_zero t).mp hzero)
  have hsub_lt :
      PeriodicHypercubicEvenSideLength H - t.val <
        PeriodicHypercubicEvenSideLength H := by
    have hlt := ZMod.val_lt t
    omega
  have htcast :
      ((t.val : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) = t :=
    ZMod.natCast_zmod_val t
  have hneg :
      -t =
        ((PeriodicHypercubicEvenSideLength H - t.val : ℕ) :
          ZMod (PeriodicHypercubicEvenSideLength H)) := by
    calc
      -t = -((t.val : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) :=
        congrArg Neg.neg htcast.symm
      _ = ((PeriodicHypercubicEvenSideLength H - t.val : ℕ) :
          ZMod (PeriodicHypercubicEvenSideLength H)) := by
        rw [Nat.cast_sub (ZMod.val_le t)]
        simp
  rw [hneg, ZMod.val_natCast_of_lt hsub_lt]

/-- A periodic time belongs to the strict negative open half exactly when its
canonical residue lies strictly above the antipodal fixed slice `H+1`. -/
theorem periodicHypercubicEvenStrictNegativeTime_iff_val
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    periodicHypercubicEvenStrictNegativeTime H t ↔
      H + 1 < t.val := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  unfold periodicHypercubicEvenStrictNegativeTime
  rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
  by_cases ht : t = 0
  · subst t
    simp
  · rw [periodicHypercubicEven_neg_val_of_ne_zero H t ht]
    have hlt := ZMod.val_lt t
    have htval_pos : 0 < t.val := by
      apply Nat.pos_of_ne_zero
      intro hzero
      exact ht ((ZMod.val_eq_zero t).mp hzero)
    simp only [PeriodicHypercubicEvenSideLength] at hlt ⊢
    omega

/-- The complement of the two strict open half-tori consists exactly of the
primary and antipodal reflection-fixed time slices. -/
theorem periodicHypercubicEven_not_openTime_iff_primary_or_antipodal
    (H : ℕ)
    (t : ZMod (PeriodicHypercubicEvenSideLength H)) :
    (¬ periodicHypercubicEvenStrictPositiveTime H t ∧
      ¬ periodicHypercubicEvenStrictNegativeTime H t) ↔
      t = 0 ∨
        t = ((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H)) := by
  letI : NeZero (PeriodicHypercubicEvenSideLength H) := ⟨by
    simp [PeriodicHypercubicEvenSideLength]⟩
  constructor
  · rintro ⟨hpos, hneg⟩
    have hpos' : ¬ (1 ≤ t.val ∧ t.val ≤ H) := by
      simpa [periodicHypercubicEvenStrictPositiveTime_iff_val] using hpos
    have hneg' : ¬ H + 1 < t.val := by
      simpa [periodicHypercubicEvenStrictNegativeTime_iff_val] using hneg
    have hlt := ZMod.val_lt t
    have hval : t.val = 0 ∨ t.val = H + 1 := by
      simp only [PeriodicHypercubicEvenSideLength] at hlt
      omega
    rcases hval with hzero | hhalf
    · exact Or.inl ((ZMod.val_eq_zero t).mp hzero)
    · right
      rw [← ZMod.natCast_zmod_val t]
      exact congrArg
        (fun a : ℕ => (a : ZMod (PeriodicHypercubicEvenSideLength H))) hhalf
  · rintro (rfl | rfl)
    · constructor
      · rw [periodicHypercubicEvenStrictPositiveTime_iff_val]
        simp
      · rw [periodicHypercubicEvenStrictNegativeTime_iff_val]
        simp
    · have hhalf_lt : H + 1 < PeriodicHypercubicEvenSideLength H := by
        simp only [PeriodicHypercubicEvenSideLength]
        omega
      have hval :
          (((H + 1 : ℕ) : ZMod (PeriodicHypercubicEvenSideLength H))).val =
            H + 1 :=
        ZMod.val_natCast_of_lt hhalf_lt
      constructor
      · rw [periodicHypercubicEvenStrictPositiveTime_iff_val, hval]
        omega
      · rw [periodicHypercubicEvenStrictNegativeTime_iff_val, hval]
        omega

/-- A vertex lies outside both open half-tori exactly when it lies on one of
the two reflection-fixed time slices. -/
theorem periodicHypercubicEvenVertex_not_openHalf_iff_on_fixedPlane
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H) :
    (¬ periodicHypercubicEvenStrictPositiveVertex H v ∧
      ¬ periodicHypercubicEvenStrictNegativeVertex H v) ↔
      periodicHypercubicEvenOnPrimaryReflectionPlane H v ∨
        periodicHypercubicEvenOnAntipodalReflectionPlane H v := by
  exact periodicHypercubicEven_not_openTime_iff_primary_or_antipodal H (v 0)

/-- A spatial crossing plaquette is exactly a time-free plaquette based on one
of the two reflection-fixed slices. -/
theorem periodicHypercubicEvenSpatialCrossingPlaquette_iff_on_fixedPlane
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H) :
    periodicHypercubicEvenSpatialCrossingPlaquette p ↔
      ¬ periodicHypercubicEvenPlaquetteHasTimeDirection p ∧
        (periodicHypercubicEvenOnPrimaryReflectionPlane H p.1 ∨
          periodicHypercubicEvenOnAntipodalReflectionPlane H p.1) := by
  rw [periodicHypercubicEvenSpatialCrossingPlaquette_iff_base_not_openHalf]
  rw [periodicHypercubicEvenVertex_not_openHalf_iff_on_fixedPlane]

end

end MathlibAnalytic
end MGAP4D
