import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonCanonicalDobrushinMatrix

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Dimensionless heat-bath coercivity supplied by a strict orientation-correct
Dobrushin coefficient. -/
def finiteOrientedLatticeWilsonDobrushinHeatBathGap
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) : ℝ :=
  1 - D.dobrushinCoefficient

/-- Standard random-scan rate associated with an orientation-correct
Dobrushin matrix: `rho = 1 - (1 - alpha) / |E|`. -/
def finiteOrientedLatticeWilsonDobrushinRandomScanRate
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) : ℝ :=
  1 - finiteOrientedLatticeWilsonDobrushinHeatBathGap D /
    (Fintype.card L.Edge : ℝ)

/-- Strict orientation-correct Dobrushin uniqueness gives a positive heat-bath
gap. -/
theorem finite_oriented_dobrushinHeatBathGap_pos
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    0 < finiteOrientedLatticeWilsonDobrushinHeatBathGap D := by
  unfold finiteOrientedLatticeWilsonDobrushinHeatBathGap
  exact sub_pos.mpr D.dobrushinCoefficient_lt_one

/-- For a nonempty physical-link set, the orientation-correct random-scan rate
is nonnegative. -/
theorem finite_oriented_dobrushinRandomScanRate_nonneg
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ finiteOrientedLatticeWilsonDobrushinRandomScanRate L D := by
  have hCardPos : (0 : ℝ) < (Fintype.card L.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hCardOne : (1 : ℝ) ≤ (Fintype.card L.Edge : ℝ) := by
    exact_mod_cast hEdge
  have hGapLeOne :
      finiteOrientedLatticeWilsonDobrushinHeatBathGap D ≤ 1 := by
    unfold finiteOrientedLatticeWilsonDobrushinHeatBathGap
    linarith [D.dobrushinCoefficient_nonneg]
  have hGapLeCard :
      finiteOrientedLatticeWilsonDobrushinHeatBathGap D ≤
        (Fintype.card L.Edge : ℝ) :=
    le_trans hGapLeOne hCardOne
  have hDivLeOne :
      finiteOrientedLatticeWilsonDobrushinHeatBathGap D /
          (Fintype.card L.Edge : ℝ) ≤ 1 :=
    (div_le_one hCardPos).2 hGapLeCard
  unfold finiteOrientedLatticeWilsonDobrushinRandomScanRate
  linarith

/-- For a nonempty physical-link set, the orientation-correct random-scan rate
is strictly below one. -/
theorem finite_oriented_dobrushinRandomScanRate_lt_one
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedLatticeWilsonDobrushinRandomScanRate L D < 1 := by
  have hCardPos : (0 : ℝ) < (Fintype.card L.Edge : ℝ) :=
    Nat.cast_pos.mpr hEdge
  have hQuotPos :
      0 < finiteOrientedLatticeWilsonDobrushinHeatBathGap D /
        (Fintype.card L.Edge : ℝ) :=
    div_pos (finite_oriented_dobrushinHeatBathGap_pos D) hCardPos
  unfold finiteOrientedLatticeWilsonDobrushinRandomScanRate
  linarith

/-- Random-scan normalization recovers the unnormalized oriented heat-bath gap
exactly. -/
theorem finite_oriented_edgeCard_mul_one_sub_dobrushinRandomScanRate
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    (Fintype.card L.Edge : ℝ) *
        (1 - finiteOrientedLatticeWilsonDobrushinRandomScanRate L D) =
      finiteOrientedLatticeWilsonDobrushinHeatBathGap D := by
  have hCard : (Fintype.card L.Edge : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hEdge)
  unfold finiteOrientedLatticeWilsonDobrushinRandomScanRate
  field_simp [hCard]
  ring

/-- The orientation-correct random-scan rate lies in the Markov interval
`[0,1)`. -/
theorem finite_oriented_dobrushinRandomScanRate_mem
    (L : FiniteOrientedLatticeWilsonSystem)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedLatticeWilsonDobrushinRandomScanRate L D ∈
      Set.Ico (0 : ℝ) 1 :=
  ⟨finite_oriented_dobrushinRandomScanRate_nonneg L D hEdge,
    finite_oriented_dobrushinRandomScanRate_lt_one L D hEdge⟩

end

end MathlibAnalytic
end MGAP4D
