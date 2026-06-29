import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonRandomScanVariationProfile

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Dobrushin contraction factor for the exact compact random-scan heat-bath
operator. -/
def continuousCompactOrientedGaugeWilsonRandomScanContractionFactor
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C) : ℝ :=
  1 - (1 - D.dobrushinCoefficient) /
    Fintype.card C.base.geometry.Edge

/-- Averaging the one-link Dobrushin updates contracts total physical-link
variation by the exact random-scan factor. -/
theorem continuous_compact_oriented_randomScanUpdatedVariation_total_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonRandomScanUpdatedVariation
          D variation) ≤
      continuousCompactOrientedGaugeWilsonRandomScanContractionFactor D *
        continuousCompactOrientedGaugeWilsonTotalVariation variation := by
  let n : ℝ := Fintype.card C.base.geometry.Edge
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast hEdge
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hinv : 0 ≤ n⁻¹ := inv_nonneg.mpr hn.le
  unfold continuousCompactOrientedGaugeWilsonTotalVariation
    continuousCompactOrientedGaugeWilsonRandomScanUpdatedVariation
    continuousCompactOrientedGaugeWilsonRandomScanContractionFactor
  change
    (∑ source : C.base.geometry.Edge,
      n⁻¹ * ∑ target : C.base.geometry.Edge,
        continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
          D variation target source) ≤
      (1 - (1 - D.dobrushinCoefficient) / n) *
        ∑ source : C.base.geometry.Edge, variation source
  rw [← Finset.mul_sum]
  calc
    n⁻¹ * ∑ source : C.base.geometry.Edge,
        ∑ target : C.base.geometry.Edge,
          continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D variation target source =
      n⁻¹ * ∑ target : C.base.geometry.Edge,
        ∑ source : C.base.geometry.Edge,
          continuousCompactOrientedGaugeWilsonDobrushinUpdatedVariation
            D variation target source := by
      rw [Finset.sum_comm]
    _ ≤ n⁻¹ * ∑ target : C.base.geometry.Edge,
        ((∑ source : C.base.geometry.Edge, variation source) -
          (1 - D.dobrushinCoefficient) * variation target) := by
      apply mul_le_mul_of_nonneg_left _ hinv
      apply Finset.sum_le_sum
      intro target _htarget
      exact
        continuous_compact_oriented_dobrushinUpdatedVariation_total_le
          D variation hVariation target
    _ = (1 - (1 - D.dobrushinCoefficient) / n) *
        ∑ source : C.base.geometry.Edge, variation source := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        Finset.card_univ, ← Finset.mul_sum]
      change n⁻¹ *
          (n * (∑ source : C.base.geometry.Edge, variation source) -
            (1 - D.dobrushinCoefficient) *
              ∑ target : C.base.geometry.Edge, variation target) =
        (1 - (1 - D.dobrushinCoefficient) / n) *
          ∑ source : C.base.geometry.Edge, variation source
      field_simp [hn0]

/-- The exact compact random-scan heat-bath observable inherits the strict
Dobrushin total-variation contraction. -/
theorem continuous_compact_oriented_randomScanHeatBathSweep_variation_total_le
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    {O : BoundedContinuousFunction C.base.Configuration ℝ}
    (P : ContinuousCompactOrientedGaugeWilsonCenteredVariationProfile C O)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (P.randomScanVariationBound D).variation ≤
      continuousCompactOrientedGaugeWilsonRandomScanContractionFactor D *
        continuousCompactOrientedGaugeWilsonTotalVariation P.variation := by
  exact continuous_compact_oriented_randomScanUpdatedVariation_total_le
    D hEdge P.variation P.variation_nonneg

end
end MathlibAnalytic
end MGAP4D
