import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingTimeClassification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpatialCrossingBoundaryDependence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Strictly smaller geometric rank selects the positive representative of a
reflection orbit. -/
theorem finiteInvolutiveEdgeRankSide_eq_positive_of_lt
    {Edge : Type}
    (reflection : Edge → Edge)
    (rank : Edge → ℕ)
    (e : Edge)
    (hlt : rank e < rank (reflection e)) :
    finiteInvolutiveEdgeRankSide reflection rank e =
      ReflectionEdgeSide.positive := by
  simp [finiteInvolutiveEdgeRankSide, hlt]

/-- Strictly larger geometric rank selects the negative representative of a
reflection orbit. -/
theorem finiteInvolutiveEdgeRankSide_eq_negative_of_gt
    {Edge : Type}
    (reflection : Edge → Edge)
    (rank : Edge → ℕ)
    (e : Edge)
    (hgt : rank (reflection e) < rank e) :
    finiteInvolutiveEdgeRankSide reflection rank e =
      ReflectionEdgeSide.negative := by
  simp [finiteInvolutiveEdgeRankSide, hgt, not_lt_of_ge hgt.le]

/-- Equal geometric ranks select the shared fixed sector. -/
theorem finiteInvolutiveEdgeRankSide_eq_fixed_of_eq
    {Edge : Type}
    (reflection : Edge → Edge)
    (rank : Edge → ℕ)
    (e : Edge)
    (heq : rank e = rank (reflection e)) :
    finiteInvolutiveEdgeRankSide reflection rank e =
      ReflectionEdgeSide.fixed := by
  simp [finiteInvolutiveEdgeRankSide, heq]

/-- Reflection rank of a spatial link is the residue rank of the negated source
time. -/
theorem periodicHypercubicEvenEdgeTimeRank_reflection_spatial
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0) :
    periodicHypercubicEvenEdgeTimeRank H
        (periodicHypercubicEvenEdgeReflection H e) =
      (-(e.1 0)).val := by
  rw [periodicHypercubicEvenEdgeReflection_spatial H e hspace]
  simp [periodicHypercubicEvenEdgeTimeRank]

/-- Reflection rank of a positive time link is the residue rank of the negative
of the next source time. -/
theorem periodicHypercubicEvenEdgeTimeRank_reflection_time
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H) :
    periodicHypercubicEvenEdgeTimeRank H
        (periodicHypercubicEvenEdgeReflection H (v, 0)) =
      (-(v 0 + 1)).val := by
  unfold periodicHypercubicEvenEdgeTimeRank
  rw [periodicHypercubicEvenEdgeReflection_time]
  change
    (periodicHypercubicUnshift (PeriodicHypercubicEvenSideLength H)
      (periodicHypercubicEvenTimeReflection H v) 0 0).val =
      (-(v 0 + 1)).val
  congr 1
  simp [periodicHypercubicUnshift, periodicHypercubicUnit,
    periodicHypercubicEvenTimeReflection]
  abel

/-- A spatial link on the primary fixed slice belongs to the fixed edge sector. -/
theorem periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hzero : (e.1 0).val = 0) :
    periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed := by
  apply finiteInvolutiveEdgeRankSide_eq_fixed_of_eq
  rw [periodicHypercubicEvenEdgeTimeRank_reflection_spatial H e hspace]
  unfold periodicHypercubicEvenEdgeTimeRank
  have ht : e.1 0 = 0 := (ZMod.val_eq_zero _).mp hzero
  simp [ht, hzero]

/-- A spatial link with source time in `1, ..., H` belongs to the positive edge
sector. -/
theorem periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hpos : 1 ≤ (e.1 0).val)
    (hle : (e.1 0).val ≤ H) :
    periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.positive := by
  apply finiteInvolutiveEdgeRankSide_eq_positive_of_lt
  rw [periodicHypercubicEvenEdgeTimeRank_reflection_spatial H e hspace]
  unfold periodicHypercubicEvenEdgeTimeRank
  have ht : e.1 0 ≠ 0 := by
    intro h
    have : (e.1 0).val = 0 := by simp [h]
    omega
  rw [periodicHypercubicEven_neg_val_of_ne_zero H (e.1 0) ht]
  simp only [PeriodicHypercubicEvenSideLength]
  omega

/-- A spatial link on the antipodal fixed slice belongs to the fixed edge
sector. -/
theorem periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_half
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hhalf : (e.1 0).val = H + 1) :
    periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.fixed := by
  apply finiteInvolutiveEdgeRankSide_eq_fixed_of_eq
  rw [periodicHypercubicEvenEdgeTimeRank_reflection_spatial H e hspace]
  unfold periodicHypercubicEvenEdgeTimeRank
  have ht : e.1 0 ≠ 0 := by
    intro h
    have : (e.1 0).val = 0 := by simp [h]
    omega
  rw [periodicHypercubicEven_neg_val_of_ne_zero H (e.1 0) ht]
  simp only [PeriodicHypercubicEvenSideLength]
  omega

/-- A spatial link strictly beyond the antipodal fixed slice belongs to the
negative edge sector. -/
theorem periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hneg : H + 1 < (e.1 0).val) :
    periodicHypercubicEvenEdgeSide H e = ReflectionEdgeSide.negative := by
  apply finiteInvolutiveEdgeRankSide_eq_negative_of_gt
  rw [periodicHypercubicEvenEdgeTimeRank_reflection_spatial H e hspace]
  unfold periodicHypercubicEvenEdgeTimeRank
  have ht : e.1 0 ≠ 0 := by
    intro h
    have : (e.1 0).val = 0 := by simp [h]
    omega
  rw [periodicHypercubicEven_neg_val_of_ne_zero H (e.1 0) ht]
  have hlt := ZMod.val_lt (e.1 0)
  simp only [PeriodicHypercubicEvenSideLength] at hlt ⊢
  omega

/-- A spatial link at or before the antipodal fixed slice is never in the
negative edge sector. -/
theorem periodicHypercubicEvenEdgeSide_spatial_ne_negative_of_val_le_half
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hle : (e.1 0).val ≤ H + 1) :
    periodicHypercubicEvenEdgeSide H e ≠ ReflectionEdgeSide.negative := by
  by_cases hzero : (e.1 0).val = 0
  · rw [periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
      H e hspace hzero]
    decide
  · by_cases hhalf : (e.1 0).val = H + 1
    · rw [periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_half
        H e hspace hhalf]
      decide
    · have hpos : 1 ≤ (e.1 0).val := Nat.one_le_iff_ne_zero.2 hzero
      have hH : (e.1 0).val ≤ H := by omega
      rw [periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
        H e hspace hpos hH]
      decide

/-- A spatial link at the primary fixed slice or on the negative side is never
in the positive edge sector. -/
theorem periodicHypercubicEvenEdgeSide_spatial_ne_positive_of_zero_or_half_le_val
    (H : ℕ)
    (e : PeriodicHypercubicEvenEdge H)
    (hspace : e.2 ≠ 0)
    (hregion : (e.1 0).val = 0 ∨ H + 1 ≤ (e.1 0).val) :
    periodicHypercubicEvenEdgeSide H e ≠ ReflectionEdgeSide.positive := by
  rcases hregion with hzero | hhalf
  · rw [periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_zero
      H e hspace hzero]
    decide
  · by_cases heq : (e.1 0).val = H + 1
    · rw [periodicHypercubicEvenEdgeSide_spatial_eq_fixed_of_val_eq_half
        H e hspace heq]
      decide
    · have hlt : H + 1 < (e.1 0).val := lt_of_le_of_ne hhalf (Ne.symm heq)
      rw [periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
        H e hspace hlt]
      decide

/-- A positive time link based at a residue in `0, ..., H` belongs to the
positive edge sector. -/
theorem periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    (hle : (v 0).val ≤ H) :
    periodicHypercubicEvenEdgeSide H (v, 0) =
      ReflectionEdgeSide.positive := by
  apply finiteInvolutiveEdgeRankSide_eq_positive_of_lt
  rw [periodicHypercubicEvenEdgeTimeRank_reflection_time H v]
  unfold periodicHypercubicEvenEdgeTimeRank
  have hnowrap : (v 0).val + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hnext := periodicHypercubicEven_val_add_one_of_lt H (v 0) hnowrap
  have hnext_ne : v 0 + 1 ≠ 0 := by
    intro hzero
    have hz := congrArg ZMod.val hzero
    rw [hnext] at hz
    simp at hz
  rw [periodicHypercubicEven_neg_val_of_ne_zero H (v 0 + 1) hnext_ne]
  rw [hnext]
  simp only [PeriodicHypercubicEvenSideLength]
  omega

/-- A positive time link based at or beyond the antipodal fixed slice belongs
to the negative edge sector. -/
theorem periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
    (H : ℕ)
    (v : PeriodicHypercubicEvenVertex H)
    (hhalf : H + 1 ≤ (v 0).val) :
    periodicHypercubicEvenEdgeSide H (v, 0) =
      ReflectionEdgeSide.negative := by
  apply finiteInvolutiveEdgeRankSide_eq_negative_of_gt
  rw [periodicHypercubicEvenEdgeTimeRank_reflection_time H v]
  unfold periodicHypercubicEvenEdgeTimeRank
  by_cases hnowrap : (v 0).val + 1 < PeriodicHypercubicEvenSideLength H
  · have hnext := periodicHypercubicEven_val_add_one_of_lt H (v 0) hnowrap
    have hnext_ne : v 0 + 1 ≠ 0 := by
      intro hzero
      have hz := congrArg ZMod.val hzero
      rw [hnext] at hz
      simp at hz
    rw [periodicHypercubicEven_neg_val_of_ne_zero H (v 0 + 1) hnext_ne]
    rw [hnext]
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  · have hnext := periodicHypercubicEven_val_add_one_of_not_lt H (v 0) hnowrap
    have hzero : v 0 + 1 = 0 := (ZMod.val_eq_zero _).mp hnext
    have hpos : 0 < (v 0).val := by omega
    simpa [hzero] using hpos

end

end MathlibAnalytic
end MGAP4D
