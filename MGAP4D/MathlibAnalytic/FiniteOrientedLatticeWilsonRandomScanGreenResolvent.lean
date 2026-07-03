import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonDobrushinSpatialCovarianceBridge
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The Dobrushin Green kernel applied on the right to a nonnegative linkwise
variation profile. -/
noncomputable def
    FiniteOrientedLatticeWilsonDobrushinMatrixData.weightedInfluenceGreen
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (source : L.Edge) : ℝ :=
  ∑ target : L.Edge,
    variation target * D.influenceGreenTail 0 target source

/-- A nonnegative variation profile produces a nonnegative weighted Green
profile. -/
theorem finite_oriented_weightedInfluenceGreen_nonneg
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (hVariation : ∀ e : L.Edge, 0 ≤ variation e)
    (source : L.Edge) :
    0 ≤ D.weightedInfluenceGreen variation source := by
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.weightedInfluenceGreen
  exact Finset.sum_nonneg fun target _hTarget =>
    mul_nonneg (hVariation target)
      (finite_oriented_influenceGreenTail_nonneg D 0 target source)

/-- The full pointwise Green kernel is the identity kernel plus one influence
step appended on the right. -/
theorem finite_oriented_influenceGreenTail_zero_eq_identity_add
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (target source : L.Edge) :
    D.influenceGreenTail 0 target source =
      (if target = source then 1 else 0) +
        ∑ middle : L.Edge,
          D.influenceGreenTail 0 target middle *
            D.influence middle source := by
  classical
  have hSummable : Summable fun m : ℕ =>
      D.influencePathKernel m target source := by
    simpa using
      (finite_oriented_influenceGreenTail_summable
        D 0 target source)
  have hShift := hSummable.tsum_eq_zero_add
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.influenceGreenTail
  rw [hShift]
  congr 1
  · simp [FiniteOrientedLatticeWilsonDobrushinMatrixData.influencePathKernel]
  · simp_rw [finite_oriented_influencePathKernel_succ]
    rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro middle _hMiddle
    rw [tsum_mul_right]
    rfl

/-- The weighted Green profile solves the right resolvent equation
`Gv = v + (Gv) C`. -/
theorem finite_oriented_weightedInfluenceGreen_eq_add_influence
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (source : L.Edge) :
    D.weightedInfluenceGreen variation source =
      variation source +
        ∑ middle : L.Edge,
          D.weightedInfluenceGreen variation middle *
            D.influence middle source := by
  classical
  unfold
    FiniteOrientedLatticeWilsonDobrushinMatrixData.weightedInfluenceGreen
  simp_rw [finite_oriented_influenceGreenTail_zero_eq_identity_add]
  calc
    (∑ target : L.Edge,
      variation target *
        ((if target = source then 1 else 0) +
          ∑ middle : L.Edge,
            D.influenceGreenTail 0 target middle *
              D.influence middle source)) =
      (∑ target : L.Edge,
        variation target * (if target = source then 1 else 0)) +
        ∑ target : L.Edge,
          variation target *
            ∑ middle : L.Edge,
              D.influenceGreenTail 0 target middle *
                D.influence middle source := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro target _hTarget
      ring
    _ = variation source +
        ∑ target : L.Edge,
          ∑ middle : L.Edge,
            variation target *
              (D.influenceGreenTail 0 target middle *
                D.influence middle source) := by
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro target _hTarget
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro middle _hMiddle
        ring
    _ = variation source +
        ∑ middle : L.Edge,
          ∑ target : L.Edge,
            variation target *
              (D.influenceGreenTail 0 target middle *
                D.influence middle source) := by
      rw [Finset.sum_comm]
    _ = variation source +
        ∑ middle : L.Edge,
          (∑ target : L.Edge,
            variation target *
              D.influenceGreenTail 0 target middle) *
                D.influence middle source := by
      congr 1
      apply Finset.sum_congr rfl
      intro middle _hMiddle
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro target _hTarget
      ring

/-- Exact fixed-source expansion of one random-scan variation update. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_eq_erase
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (variation : L.Edge → ℝ)
    (source : L.Edge) :
    finiteOrientedConditionalAverageRandomScanVariation D variation source =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        (((Finset.univ.erase source).card : ℝ) * variation source +
          ∑ target : L.Edge,
            D.influence target source * variation target) := by
  classical
  unfold finiteOrientedConditionalAverageRandomScanVariation
  have hSplit := Finset.sum_erase_add
    (s := (Finset.univ : Finset L.Edge))
    (f := fun target =>
      finiteOrientedConditionalAverageUpdatedVariation
        D variation target source)
    (Finset.mem_univ source)
  have hDiag :
      finiteOrientedConditionalAverageUpdatedVariation
        D variation source source = 0 := by
    simp [finiteOrientedConditionalAverageUpdatedVariation]
  have hOff :
      (∑ target ∈ (Finset.univ.erase source),
        finiteOrientedConditionalAverageUpdatedVariation
          D variation target source) =
      ((Finset.univ.erase source).card : ℝ) * variation source +
        ∑ target ∈ (Finset.univ.erase source),
          D.influence target source * variation target := by
    simp_rw [finiteOrientedConditionalAverageUpdatedVariation]
    have hNe : ∀ target ∈ (Finset.univ.erase source), source ≠ target := by
      intro target hTarget
      exact (Finset.ne_of_mem_erase hTarget).symm
    simp_rw [if_neg (hNe _ ‹_›)]
    rw [Finset.sum_add_distrib]
    simp
  have hInfluenceErase :
      (∑ target ∈ (Finset.univ.erase source),
        D.influence target source * variation target) =
      ∑ target : L.Edge,
        D.influence target source * variation target := by
    have h := Finset.sum_erase_add
      (s := (Finset.univ : Finset L.Edge))
      (f := fun target => D.influence target source * variation target)
      (Finset.mem_univ source)
    rw [D.influence_diagonal_zero source, zero_mul, add_zero] at h
    exact h
  rw [← hSplit, hDiag, add_zero, hOff, hInfluenceErase]

/-- Random-scan variation propagation is monotone. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_mono
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (u v : L.Edge → ℝ)
    (hUV : ∀ e : L.Edge, u e ≤ v e)
    (source : L.Edge) :
    finiteOrientedConditionalAverageRandomScanVariation D u source ≤
      finiteOrientedConditionalAverageRandomScanVariation D v source := by
  classical
  unfold finiteOrientedConditionalAverageRandomScanVariation
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro target _hTarget
  unfold finiteOrientedConditionalAverageUpdatedVariation
  by_cases hEq : source = target
  · simp [hEq]
  · simp only [hEq, if_false]
    exact add_le_add (hUV source)
      (mul_le_mul_of_nonneg_left
        (hUV target) (D.influence_nonneg target source))

/-- Random-scan variation propagation commutes with finite sums of variation
profiles. -/
theorem finiteOrientedConditionalAverageRandomScanVariation_finset_sum
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    {ι : Type*}
    (s : Finset ι)
    (variation : ι → L.Edge → ℝ)
    (source : L.Edge) :
    finiteOrientedConditionalAverageRandomScanVariation D
        (fun e => ∑ i ∈ s, variation i e) source =
      ∑ i ∈ s,
        finiteOrientedConditionalAverageRandomScanVariation D
          (variation i) source := by
  classical
  unfold finiteOrientedConditionalAverageRandomScanVariation
  rw [Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro target _hTarget
  unfold finiteOrientedConditionalAverageUpdatedVariation
  by_cases hEq : source = target
  · simp [hEq]
  · simp only [hEq, if_false]
    rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Multiplying the weighted Green profile by the number of physical links gives
an exact supersolution for one uniform random-scan variation update. -/
theorem finite_oriented_randomScanVariation_green_supersolution
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (variation : L.Edge → ℝ)
    (source : L.Edge) :
    variation source +
      finiteOrientedConditionalAverageRandomScanVariation D
        (fun e =>
          (Fintype.card L.Edge : ℝ) *
            D.weightedInfluenceGreen variation e) source =
      (Fintype.card L.Edge : ℝ) *
        D.weightedInfluenceGreen variation source := by
  classical
  let N : ℝ := Fintype.card L.Edge
  let G : L.Edge → ℝ := D.weightedInfluenceGreen variation
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast (Nat.ne_of_gt hEdge)
  have hEraseCardNat :
      (Finset.univ.erase source).card + 1 = Fintype.card L.Edge := by
    simpa using Finset.card_erase_add_one (Finset.mem_univ source)
  have hEraseCardReal :
      ((Finset.univ.erase source).card : ℝ) = N - 1 := by
    exact_mod_cast hEraseCardNat
  rw [finiteOrientedConditionalAverageRandomScanVariation_eq_erase]
  change variation source + N⁻¹ *
      (((Finset.univ.erase source).card : ℝ) * (N * G source) +
        ∑ target : L.Edge,
          D.influence target source * (N * G target)) =
    N * G source
  rw [hEraseCardReal]
  have hGreen :=
    finite_oriented_weightedInfluenceGreen_eq_add_influence
      D variation source
  change G source = variation source +
      ∑ middle : L.Edge, G middle * D.influence middle source at hGreen
  have hSum :
      (∑ target : L.Edge,
        D.influence target source * (N * G target)) =
      N * ∑ target : L.Edge,
        G target * D.influence target source := by
    calc
      (∑ target : L.Edge,
        D.influence target source * (N * G target)) =
        ∑ target : L.Edge,
          N * (G target * D.influence target source) := by
          apply Finset.sum_congr rfl
          intro target _hTarget
          ring
      _ = N * ∑ target : L.Edge,
          G target * D.influence target source := by
        rw [Finset.mul_sum]
  rw [hSum]
  field_simp [hN]
  nlinarith [hGreen]

/-- Partial sums of the iterated random-scan variation profile are bounded by
`N` times the weighted Dobrushin Green profile. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_sum_range_le_green
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (n : ℕ)
    (source : L.Edge) :
    (∑ k ∈ Finset.range n,
      P.randomScanConditionalAverageVariationIterate D k source) ≤
      (Fintype.card L.Edge : ℝ) *
        D.weightedInfluenceGreen P.variation source := by
  classical
  let H : L.Edge → ℝ := fun e =>
    (Fintype.card L.Edge : ℝ) *
      D.weightedInfluenceGreen P.variation e
  have hHNonneg : ∀ e : L.Edge, 0 ≤ H e := by
    intro e
    exact mul_nonneg (Nat.cast_nonneg _)
      (finite_oriented_weightedInfluenceGreen_nonneg
        D P.variation P.variation_nonneg e)
  have hSup : ∀ e : L.Edge,
      P.variation e +
        finiteOrientedConditionalAverageRandomScanVariation D H e = H e := by
    intro e
    exact finite_oriented_randomScanVariation_green_supersolution
      D hEdge P.variation e
  induction n with
  | zero =>
      simp [H, hHNonneg source]
  | succ n ih =>
      have hRec :
          (∑ k ∈ Finset.range (n + 1),
            P.randomScanConditionalAverageVariationIterate D k source) =
          P.variation source +
            finiteOrientedConditionalAverageRandomScanVariation D
              (fun e => ∑ k ∈ Finset.range n,
                P.randomScanConditionalAverageVariationIterate D k e)
              source := by
        induction n with
        | zero => simp
        | succ n hn =>
            simp only [Finset.sum_range_succ,
              FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate_succ]
            rw [hn]
            rw [finiteOrientedConditionalAverageRandomScanVariation_finset_sum]
            simp [Finset.sum_range_succ]
      rw [hRec]
      calc
        P.variation source +
            finiteOrientedConditionalAverageRandomScanVariation D
              (fun e => ∑ k ∈ Finset.range n,
                P.randomScanConditionalAverageVariationIterate D k e)
              source ≤
          P.variation source +
            finiteOrientedConditionalAverageRandomScanVariation D H source := by
              apply add_le_add_left
              apply finiteOrientedConditionalAverageRandomScanVariation_mono
              intro e
              exact ih e
        _ = H source := hSup source

/-- The normalized all-time random-scan variation resolvent is dominated
pointwise by the Dobrushin Green kernel applied to the initial variation. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationResolvent_le_green
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (source : L.Edge) :
    (Fintype.card L.Edge : ℝ)⁻¹ *
        (∑' k : ℕ,
          P.randomScanConditionalAverageVariationIterate D k source) ≤
      D.weightedInfluenceGreen P.variation source := by
  have hTsum :
      (∑' k : ℕ,
        P.randomScanConditionalAverageVariationIterate D k source) ≤
      (Fintype.card L.Edge : ℝ) *
        D.weightedInfluenceGreen P.variation source :=
    Real.tsum_le_of_sum_range_le
      (fun k =>
        (P.randomScanConditionalAverageCenteredVariationIterate D k)
          |>.variation_nonneg source)
      (fun n =>
        P.randomScanConditionalAverageVariationIterate_sum_range_le_green
          D hEdge n source)
  have hInvNonneg : 0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hCardNe : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  calc
    (Fintype.card L.Edge : ℝ)⁻¹ *
        (∑' k : ℕ,
          P.randomScanConditionalAverageVariationIterate D k source) ≤
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ((Fintype.card L.Edge : ℝ) *
          D.weightedInfluenceGreen P.variation source) :=
      mul_le_mul_of_nonneg_left hTsum hInvNonneg
    _ = D.weightedInfluenceGreen P.variation source := by
      field_simp [hCardNe]

end

end MathlibAnalytic
end MGAP4D
