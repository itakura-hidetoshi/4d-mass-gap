import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenTemporalCrossingHalfSectors

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Canonical residue bounds for a strictly positive vertex. -/
theorem periodicHypercubicEvenStrictPositiveVertex_val
    {H : ℕ}
    {v : PeriodicHypercubicEvenVertex H}
    (hv : periodicHypercubicEvenStrictPositiveVertex H v) :
    1 ≤ (v 0).val ∧ (v 0).val ≤ H := by
  exact
    (periodicHypercubicEvenStrictPositiveTime_iff_val H (v 0)).1 hv

/-- Canonical residue bound for a strictly negative vertex. -/
theorem periodicHypercubicEvenStrictNegativeVertex_val
    {H : ℕ}
    {v : PeriodicHypercubicEvenVertex H}
    (hv : periodicHypercubicEvenStrictNegativeVertex H v) :
    H + 1 < (v 0).val := by
  exact
    (periodicHypercubicEvenStrictNegativeTime_iff_val H (v 0)).1 hv

/-- Every physical link in the signed boundary of a strictly positive
plaquette is a positive reflection-orbit representative. -/
theorem periodicHypercubicEvenStrictPositivePlaquette_boundaryStep_side_positive
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenStrictPositivePlaquette p)
    (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p k).edge =
      ReflectionEdgeSide.positive := by
  have hbase : periodicHypercubicEvenStrictPositiveVertex H p.1 :=
    hp p.1 (by
      simp [periodicHypercubicEvenPlaquetteVertices,
        periodicHypercubicEvenPlaquetteCorner00])
  have h10 : periodicHypercubicEvenStrictPositiveVertex H
      (periodicHypercubicEvenPlaquetteCorner10 p) :=
    hp _ (by simp [periodicHypercubicEvenPlaquetteVertices])
  have h01 : periodicHypercubicEvenStrictPositiveVertex H
      (periodicHypercubicEvenPlaquetteCorner01 p) :=
    hp _ (by simp [periodicHypercubicEvenPlaquetteVertices])
  have hbaseVal := periodicHypercubicEvenStrictPositiveVertex_val hbase
  have h10Val := periodicHypercubicEvenStrictPositiveVertex_val h10
  have h01Val := periodicHypercubicEvenStrictPositiveVertex_val h01
  have hnu : periodicHypercubicPlaquetteSecondAxis p ≠ 0 :=
    periodicHypercubicPlaquetteSecondAxis_ne_zero p
  change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).edge =
    ReflectionEdgeSide.positive
  fin_cases k
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteFirstAxis p) =
        ReflectionEdgeSide.positive
    by_cases hmu : periodicHypercubicPlaquetteFirstAxis p = 0
    · rw [hmu]
      exact periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
        H p.1 hbaseVal.2
    · exact periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
        H _ hmu hbaseVal.1 hbaseVal.2
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner10 p,
        periodicHypercubicPlaquetteSecondAxis p) =
        ReflectionEdgeSide.positive
    exact periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
      H _ hnu h10Val.1 h10Val.2
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner01 p,
        periodicHypercubicPlaquetteFirstAxis p) =
        ReflectionEdgeSide.positive
    by_cases hmu : periodicHypercubicPlaquetteFirstAxis p = 0
    · rw [hmu]
      exact periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
        H _ h01Val.2
    · exact periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
        H _ hmu h01Val.1 h01Val.2
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteSecondAxis p) =
        ReflectionEdgeSide.positive
    exact periodicHypercubicEvenEdgeSide_spatial_eq_positive_of_val
      H _ hnu hbaseVal.1 hbaseVal.2

/-- Every physical link in the signed boundary of a strictly negative
plaquette is a negative reflection-orbit representative. -/
theorem periodicHypercubicEvenStrictNegativePlaquette_boundaryStep_side_negative
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenStrictNegativePlaquette p)
    (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p k).edge =
      ReflectionEdgeSide.negative := by
  have hbase : periodicHypercubicEvenStrictNegativeVertex H p.1 :=
    hp p.1 (by
      simp [periodicHypercubicEvenPlaquetteVertices,
        periodicHypercubicEvenPlaquetteCorner00])
  have h10 : periodicHypercubicEvenStrictNegativeVertex H
      (periodicHypercubicEvenPlaquetteCorner10 p) :=
    hp _ (by simp [periodicHypercubicEvenPlaquetteVertices])
  have h01 : periodicHypercubicEvenStrictNegativeVertex H
      (periodicHypercubicEvenPlaquetteCorner01 p) :=
    hp _ (by simp [periodicHypercubicEvenPlaquetteVertices])
  have hbaseVal := periodicHypercubicEvenStrictNegativeVertex_val hbase
  have h10Val := periodicHypercubicEvenStrictNegativeVertex_val h10
  have h01Val := periodicHypercubicEvenStrictNegativeVertex_val h01
  have hnu : periodicHypercubicPlaquetteSecondAxis p ≠ 0 :=
    periodicHypercubicPlaquetteSecondAxis_ne_zero p
  change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).edge =
    ReflectionEdgeSide.negative
  fin_cases k
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteFirstAxis p) =
        ReflectionEdgeSide.negative
    by_cases hmu : periodicHypercubicPlaquetteFirstAxis p = 0
    · rw [hmu]
      exact periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
        H p.1 hbaseVal.le
    · exact periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
        H _ hmu hbaseVal
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner10 p,
        periodicHypercubicPlaquetteSecondAxis p) =
        ReflectionEdgeSide.negative
    exact periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
      H _ hnu h10Val
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner01 p,
        periodicHypercubicPlaquetteFirstAxis p) =
        ReflectionEdgeSide.negative
    by_cases hmu : periodicHypercubicPlaquetteFirstAxis p = 0
    · rw [hmu]
      exact periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
        H _ h01Val.le
    · exact periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
        H _ hmu h01Val
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteSecondAxis p) =
        ReflectionEdgeSide.negative
    exact periodicHypercubicEvenEdgeSide_spatial_eq_negative_of_half_lt_val
      H _ hnu hbaseVal

/-- Every boundary link of a positive-boundary temporal plaquette is either
positive or fixed, and therefore never negative. -/
theorem periodicHypercubicEvenPositiveBoundaryTemporalPlaquette_boundaryStep_side_ne_negative
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenPositiveBoundaryTemporalPlaquette p)
    (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p k).edge ≠
      ReflectionEdgeSide.negative := by
  have htime := hp.1
  have hmu :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1
      htime
  have hnu : periodicHypercubicPlaquetteSecondAxis p ≠ 0 :=
    periodicHypercubicPlaquetteSecondAxis_ne_zero p
  have hbaseLe : (p.1 0).val ≤ H := by
    rcases hp.2 with hzero | hH <;> omega
  have hnowrap : (p.1 0).val + 1 < PeriodicHypercubicEvenSideLength H := by
    simp only [PeriodicHypercubicEvenSideLength]
    omega
  have hnext := periodicHypercubicEven_val_add_one_of_lt H (p.1 0) hnowrap
  have h10Le :
      (periodicHypercubicEvenPlaquetteCorner10 p 0).val ≤ H + 1 := by
    rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
      p htime, hnext]
    omega
  change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).edge ≠
    ReflectionEdgeSide.negative
  fin_cases k
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteFirstAxis p) ≠
        ReflectionEdgeSide.negative
    rw [hmu,
      periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
        H p.1 hbaseLe]
    decide
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner10 p,
        periodicHypercubicPlaquetteSecondAxis p) ≠
        ReflectionEdgeSide.negative
    exact
      periodicHypercubicEvenEdgeSide_spatial_ne_negative_of_val_le_half
        H _ hnu h10Le
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner01 p,
        periodicHypercubicPlaquetteFirstAxis p) ≠
        ReflectionEdgeSide.negative
    rw [hmu]
    have h01Le :
        (periodicHypercubicEvenPlaquetteCorner01 p 0).val ≤ H := by
      rw [periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
        p htime]
      exact hbaseLe
    rw [periodicHypercubicEvenEdgeSide_time_eq_positive_of_val_le
      H _ h01Le]
    decide
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteSecondAxis p) ≠
        ReflectionEdgeSide.negative
    exact
      periodicHypercubicEvenEdgeSide_spatial_ne_negative_of_val_le_half
        H _ hnu (by omega)

/-- Every boundary link of a negative-boundary temporal plaquette is either
negative or fixed, and therefore never positive. -/
theorem periodicHypercubicEvenNegativeBoundaryTemporalPlaquette_boundaryStep_side_ne_positive
    {H : ℕ}
    (p : PeriodicHypercubicEvenPlaquette H)
    (hp : periodicHypercubicEvenNegativeBoundaryTemporalPlaquette p)
    (k : Fin 4) :
    (periodicHypercubicEvenEdgeOrbitPartition H).side
        (periodicHypercubicBoundaryStep
          (PeriodicHypercubicEvenSideLength H) p k).edge ≠
      ReflectionEdgeSide.positive := by
  have htime := hp.1
  have hmu :=
    (periodicHypercubicEvenPlaquetteHasTimeDirection_iff_firstAxis_zero p).1
      htime
  have hnu : periodicHypercubicPlaquetteSecondAxis p ≠ 0 :=
    periodicHypercubicPlaquetteSecondAxis_ne_zero p
  have hbaseHalf : H + 1 ≤ (p.1 0).val := by
    rcases hp.2 with hhalf | hlast <;> omega
  have h10Region :
      (periodicHypercubicEvenPlaquetteCorner10 p 0).val = 0 ∨
        H + 1 ≤ (periodicHypercubicEvenPlaquetteCorner10 p 0).val := by
    rw [periodicHypercubicEvenPlaquetteCorner10_time_of_hasTimeDirection
      p htime]
    by_cases hnowrap : (p.1 0).val + 1 < PeriodicHypercubicEvenSideLength H
    · right
      rw [periodicHypercubicEven_val_add_one_of_lt H (p.1 0) hnowrap]
      omega
    · left
      exact periodicHypercubicEven_val_add_one_of_not_lt H (p.1 0) hnowrap
  change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicBoundaryStep
        (PeriodicHypercubicEvenSideLength H) p k).edge ≠
    ReflectionEdgeSide.positive
  fin_cases k
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteFirstAxis p) ≠
        ReflectionEdgeSide.positive
    rw [hmu,
      periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
        H p.1 hbaseHalf]
    decide
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner10 p,
        periodicHypercubicPlaquetteSecondAxis p) ≠
        ReflectionEdgeSide.positive
    exact
      periodicHypercubicEvenEdgeSide_spatial_ne_positive_of_zero_or_half_le_val
        H _ hnu h10Region
  · change periodicHypercubicEvenEdgeSide H
      (periodicHypercubicEvenPlaquetteCorner01 p,
        periodicHypercubicPlaquetteFirstAxis p) ≠
        ReflectionEdgeSide.positive
    rw [hmu]
    have h01Half :
        H + 1 ≤ (periodicHypercubicEvenPlaquetteCorner01 p 0).val := by
      rw [periodicHypercubicEvenPlaquetteCorner01_time_of_hasTimeDirection
        p htime]
      exact hbaseHalf
    rw [periodicHypercubicEvenEdgeSide_time_eq_negative_of_half_le_val
      H _ h01Half]
    decide
  · change periodicHypercubicEvenEdgeSide H
      (p.1, periodicHypercubicPlaquetteSecondAxis p) ≠
        ReflectionEdgeSide.positive
    exact
      periodicHypercubicEvenEdgeSide_spatial_ne_positive_of_zero_or_half_le_val
        H _ hnu (Or.inr hbaseHalf)

end

end MathlibAnalytic
end MGAP4D
