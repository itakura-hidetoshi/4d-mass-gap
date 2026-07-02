import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonVariationRecentering
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Iteration of the concrete uniform random-scan conditional-average observable. -/
def FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverageIterate
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) : ℕ → L.Configuration → ℝ
  | 0 => f
  | k + 1 =>
      L.randomScanConditionalAverage
        (L.randomScanConditionalAverageIterate f k)

@[simp] theorem finite_oriented_randomScanConditionalAverageIterate_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ) :
    L.randomScanConditionalAverageIterate f 0 = f := rfl

@[simp] theorem finite_oriented_randomScanConditionalAverageIterate_succ
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (k : ℕ) :
    L.randomScanConditionalAverageIterate f (k + 1) =
      L.randomScanConditionalAverage
        (L.randomScanConditionalAverageIterate f k) := rfl

/-- Repeatedly apply random-scan variation propagation and the canonical
finite-fiber recentering from the preceding layer.  The result at step `k` is a
proof-relevant centered profile for the actual observable iterate. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageCenteredVariationIterate
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    (k : ℕ) → FiniteOrientedLatticeWilsonCenteredVariationProfile L
      (L.randomScanConditionalAverageIterate f k)
  | 0 => P
  | k + 1 =>
      (P.randomScanConditionalAverageCenteredVariationIterate D k)
        |>.randomScanConditionalAverageCenteredVariationProfile D

@[simp] theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageCenteredVariationIterate_zero
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L) :
    P.randomScanConditionalAverageCenteredVariationIterate D 0 = P := rfl

/-- The linkwise variation sequence carried by the proof-relevant centered
profile iteration. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (k : ℕ)
    (source : L.Edge) : ℝ :=
  (P.randomScanConditionalAverageCenteredVariationIterate D k).variation source

@[simp] theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_zero
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (source : L.Edge) :
    P.randomScanConditionalAverageVariationIterate D 0 source =
      P.variation source := rfl

@[simp] theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_succ
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (k : ℕ)
    (source : L.Edge) :
    P.randomScanConditionalAverageVariationIterate D (k + 1) source =
      finiteOrientedConditionalAverageRandomScanVariation D
        (P.randomScanConditionalAverageVariationIterate D k) source := rfl

/-- The explicit random-scan contraction factor is nonnegative on every
nonempty finite physical-link carrier. -/
theorem finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    0 ≤ finiteOrientedConditionalAverageRandomScanContractionFactor D := by
  have hCardNat : 1 ≤ Fintype.card L.Edge :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hEdge)
  have hCardOne : (1 : ℝ) ≤ (Fintype.card L.Edge : ℝ) := by
    exact_mod_cast hCardNat
  have hGapLeOne : 1 - D.dobrushinCoefficient ≤ 1 := by
    linarith [D.dobrushinCoefficient_nonneg]
  have hGapLeCard :
      1 - D.dobrushinCoefficient ≤ (Fintype.card L.Edge : ℝ) :=
    le_trans hGapLeOne hCardOne
  have hInvNonneg : 0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hProductLe :
      (1 - D.dobrushinCoefficient) *
          (Fintype.card L.Edge : ℝ)⁻¹ ≤
        (Fintype.card L.Edge : ℝ) *
          (Fintype.card L.Edge : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right hGapLeCard hInvNonneg
  have hCardNe : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  have hProductLeOne :
      (1 - D.dobrushinCoefficient) *
          (Fintype.card L.Edge : ℝ)⁻¹ ≤ 1 := by
    calc
      (1 - D.dobrushinCoefficient) *
          (Fintype.card L.Edge : ℝ)⁻¹ ≤
        (Fintype.card L.Edge : ℝ) *
          (Fintype.card L.Edge : ℝ)⁻¹ := hProductLe
      _ = 1 := mul_inv_cancel₀ hCardNe
  unfold finiteOrientedConditionalAverageRandomScanContractionFactor
  exact sub_nonneg.mpr hProductLeOne

/-- One more random-scan step contracts the total variation mass of the
iterated proof-relevant profile. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_sum_succ_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (k : ℕ) :
    (∑ source : L.Edge,
      P.randomScanConditionalAverageVariationIterate D (k + 1) source) ≤
      finiteOrientedConditionalAverageRandomScanContractionFactor D *
        ∑ source : L.Edge,
          P.randomScanConditionalAverageVariationIterate D k source := by
  exact
    (P.randomScanConditionalAverageCenteredVariationIterate D k)
      |>.randomScanConditionalAverageCenteredVariation_sum_le D hEdge

/-- After `k` uniform random-scan updates, the total link-variation mass is
bounded by the `k`th power of the finite-volume contraction factor. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_sum_le_pow
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (k : ℕ) :
    (∑ source : L.Edge,
      P.randomScanConditionalAverageVariationIterate D k source) ≤
      (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
        ∑ source : L.Edge, P.variation source := by
  have hFactorNonneg :
      0 ≤ finiteOrientedConditionalAverageRandomScanContractionFactor D :=
    finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg
      D hEdge
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (∑ source : L.Edge,
          P.randomScanConditionalAverageVariationIterate D (k + 1) source) ≤
            finiteOrientedConditionalAverageRandomScanContractionFactor D *
              ∑ source : L.Edge,
                P.randomScanConditionalAverageVariationIterate D k source :=
          P.randomScanConditionalAverageVariationIterate_sum_succ_le
            D hEdge k
        _ ≤ finiteOrientedConditionalAverageRandomScanContractionFactor D *
              ((finiteOrientedConditionalAverageRandomScanContractionFactor D) ^ k *
                ∑ source : L.Edge, P.variation source) :=
          mul_le_mul_of_nonneg_left ih hFactorNonneg
        _ = (finiteOrientedConditionalAverageRandomScanContractionFactor D) ^
              (k + 1) * ∑ source : L.Edge, P.variation source := by
          rw [pow_succ]
          ring

/-- The contraction factor used in the iteration lies in `[0,1)` under the
proof-relevant Dobrushin hypothesis. -/
theorem finiteOrientedConditionalAverageRandomScanContractionFactor_mem_Ico
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge) :
    finiteOrientedConditionalAverageRandomScanContractionFactor D ∈
      Set.Ico (0 : ℝ) 1 :=
  ⟨finiteOrientedConditionalAverageRandomScanContractionFactor_nonneg D hEdge,
    finiteOrientedConditionalAverageRandomScanContractionFactor_lt_one D hEdge⟩

end

end MathlibAnalytic
end MGAP4D
