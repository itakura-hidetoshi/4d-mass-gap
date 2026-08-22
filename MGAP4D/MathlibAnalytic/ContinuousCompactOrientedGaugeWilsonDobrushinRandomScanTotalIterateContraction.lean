import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanFiniteResolventProfile
import Mathlib.Tactic

/-!
# Total-variation contraction along finite random-scan iterates

The one-step compact-Haar random-scan variation estimate already gives

`Tot(Uv) <= q * Tot(v)`

for nonnegative variation profiles, where `q` is the certified random-scan
Dobrushin rate.  This file records the exact finite iteration of that estimate:

`Tot(U^M v) <= q^M * Tot(v)`.

The rate is only assumed nonnegative here; the strict inequality `q < 1` and
the limiting argument are deliberately kept for the next bridge.  No covariance
limit, spatial clustering theorem, continuum limit, or Hamiltonian mass-gap
statement is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A pointwise nonnegative variation profile has nonnegative total variation. -/
theorem continuous_compact_oriented_totalVariation_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e) :
    0 ≤ continuousCompactOrientedGaugeWilsonTotalVariation variation := by
  unfold continuousCompactOrientedGaugeWilsonTotalVariation
  exact Finset.sum_nonneg fun e _ => hVariation e

/-- The total variation of every finite random-scan variation iterate is
nonnegative when the initial profile is nonnegative. -/
theorem continuous_compact_oriented_dobrushinRandomScanVariationIterate_total_nonneg
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (M : ℕ) :
    0 ≤ continuousCompactOrientedGaugeWilsonTotalVariation
      (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
        D variation M) := by
  exact
    continuous_compact_oriented_totalVariation_nonneg
      (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
        D variation M)
      (continuous_compact_oriented_dobrushinRandomScanVariationIterate_nonneg
        D variation hVariation M)

/-- Iterating the one-step compact-Haar random-scan contraction gives a sharp
finite power bound for the total variation profile. -/
theorem continuous_compact_oriented_dobrushinRandomScanVariationIterate_total_le_pow_rate_mul
    {C : ContinuousCompactOrientedGaugeWilsonSystem}
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (variation : C.base.geometry.Edge → ℝ)
    (hVariation : ∀ e : C.base.geometry.Edge, 0 ≤ variation e)
    (hEdge : 0 < Fintype.card C.base.geometry.Edge)
    (hRateNonneg :
      0 ≤ continuousCompactOrientedDobrushinRandomScanRate C D.coefficient)
    (M : ℕ) :
    continuousCompactOrientedGaugeWilsonTotalVariation
        (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
          D variation M) ≤
      (continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) ^ M *
        continuousCompactOrientedGaugeWilsonTotalVariation variation := by
  induction M with
  | zero =>
      simp [continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate]
  | succ M ih =>
      have hStep :=
        continuous_compact_oriented_dobrushinRandomScanUpdatedVariation_total_le_rate_mul
          D
          (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
            D variation M)
          (continuous_compact_oriented_dobrushinRandomScanVariationIterate_nonneg
            D variation hVariation M)
          hEdge
      calc
        continuousCompactOrientedGaugeWilsonTotalVariation
            (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
              D variation (M + 1)) =
          continuousCompactOrientedGaugeWilsonTotalVariation
            (continuousCompactOrientedGaugeWilsonDobrushinRandomScanUpdatedVariation
              D
              (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                D variation M)) := by
            rfl
        _ ≤ continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
            continuousCompactOrientedGaugeWilsonTotalVariation
              (continuousCompactOrientedGaugeWilsonDobrushinRandomScanVariationIterate
                D variation M) := hStep
        _ ≤ continuousCompactOrientedDobrushinRandomScanRate C D.coefficient *
            ((continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) ^ M *
              continuousCompactOrientedGaugeWilsonTotalVariation variation) :=
          mul_le_mul_of_nonneg_left ih hRateNonneg
        _ = (continuousCompactOrientedDobrushinRandomScanRate C D.coefficient) ^ (M + 1) *
            continuousCompactOrientedGaugeWilsonTotalVariation variation := by
          rw [pow_succ]
          ring

end

end MathlibAnalytic
end MGAP4D
