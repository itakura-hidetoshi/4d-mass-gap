import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorHarnackResponseSeed
import Mathlib.Tactic

/-!
# Uniform finite-resolvent control for the posterior Harnack seed

The canonical Harnack response seed of PR #5176 supplies concrete non-strict
posterior influence data.  This file establishes the finite quantitative
bounds needed to remove the remaining boundary dependence from the first
bootstrap update.

The key elementary facts are:

* every response-generated remote influence coefficient is at most one;
* therefore the complete non-strict influence matrix is entrywise in [0,1];
* if a nonnegative variation profile is pointwise bounded by V, one posterior
  random-scan variation step is bounded by 2 V;
* consequently the m-th variation iterate is bounded by 2^m V;
* the normalized finite resolvent is bounded by M 2^M V.

The final specialization takes V to be the exact Harnack width
exp(8 beta)-exp(-8 beta) for the target-local factor.

These are deliberately finite and coarse bounds.  They assert neither a strict
Dobrushin row sum nor a volume-uniform infinite resolvent.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance posteriorHarnackSeedFiniteResolventSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every response-generated remote influence coefficient is at most one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_le_one
    (beta epsilon : ℝ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
        beta epsilon ≤ 1 := by
  let R : ℝ := 2 * (epsilon / Real.exp (-8 * beta))
  have hden : 0 < Real.exp R + 1 := by positivity
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence
  change (Real.exp R - 1) / (Real.exp R + 1) ≤ 1
  apply (div_le_iff₀ hden).2
  linarith

/-- Every entry of the complete non-strict posterior influence profile is at
most one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_le_one
    (H : ℕ)
    (beta : ℝ)
    (epsilon :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
        H beta epsilon target source ≤ 1 := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
  by_cases hdiag : source = target
  · simp [hdiag]
  · simp only [hdiag, if_false]
    by_cases hlocal :
        periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source
    · simp [hlocal]
    · simp only [hlocal, if_false]
      exact
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteInfluence_le_one
          beta (epsilon target source)

/-- The canonical Harnack-seed influence data are entrywise bounded by one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData_influence_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
      H N hN beta hbeta B).influence target source ≤ 1 := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData_influence]
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence_le_one
      H beta
      (fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta)
      target source

/-- If a nonnegative variation profile is bounded by V and all influence
coefficients are at most one, one exact target update is bounded by 2 V. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_le_two_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (hInfluenceLe :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source ≤ 1)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
        D variation target source ≤
      2 * V := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
  by_cases hdiag : source = target
  · simp [hdiag, hV]
  · simp only [hdiag, if_false]
    calc
      variation source + D.influence target source * variation target ≤
          V + 1 * V := by
        apply add_le_add (hVariationLe source)
        calc
          D.influence target source * variation target ≤
              1 * variation target :=
            mul_le_mul_of_nonneg_right
              (hInfluenceLe target source)
              (hVariationNonneg target)
          _ ≤ 1 * V :=
            mul_le_mul_of_nonneg_left
              (hVariationLe target)
              (by norm_num)
      _ = 2 * V := by ring

/-- A uniform random-scan variation step is bounded by 2 V under the same
entrywise influence bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_le_two_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (hInfluenceLe :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source ≤ 1)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
        D variation source ≤
      2 * V := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hSum :
      (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
          D variation target source) ≤
        ∑ _target : PeriodicHypercubicEvenSpatialSliceLink H, 2 * V := by
    apply Finset.sum_le_sum
    intro target _
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation_le_two_mul
        D variation hVariationNonneg V hV hVariationLe hInfluenceLe
        target source
  have hConst :
      (∑ _target : PeriodicHypercubicEvenSpatialSliceLink H, 2 * V) =
        n * (2 * V) := by
    simp [n, nsmul_eq_mul]
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
  change
    n⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
            D variation target source) ≤
      2 * V
  calc
    n⁻¹ *
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUpdatedVariation
            D variation target source) ≤
      n⁻¹ *
        (∑ _target : PeriodicHypercubicEvenSpatialSliceLink H, 2 * V) :=
      mul_le_mul_of_nonneg_left hSum (inv_nonneg.mpr hnPos.le)
    _ = n⁻¹ * (n * (2 * V)) := by rw [hConst]
    _ = 2 * V := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hnPos), one_mul]

/-- The m-th finite random-scan variation iterate is bounded by 2^m V. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_le_pow_two_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (hInfluenceLe :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source ≤ 1)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)) :
    ∀ m source,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
          D variation m source ≤
        (2 : ℝ) ^ m * V := by
  intro m
  induction m with
  | zero =>
      intro source
      simpa using hVariationLe source
  | succ m ih =>
      intro source
      have hPrevNonneg :
          ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
            0 ≤
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
                D variation m e :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
          D variation hVariationNonneg m
      have hVm : 0 ≤ (2 : ℝ) ^ m * V :=
        mul_nonneg (pow_nonneg (by norm_num) _) hV
      have hStep :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation_le_two_mul
          D
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D variation m)
          hPrevNonneg
          ((2 : ℝ) ^ m * V)
          hVm
          ih
          hInfluenceLe
          hEdge
          source
      rw [
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_succ]
      calc
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanUpdatedVariation
            D
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D variation m)
            source ≤
          2 * ((2 : ℝ) ^ m * V) := hStep
        _ = (2 : ℝ) ^ (m + 1) * V := by
          rw [pow_succ]
          ring

/-- The finite partial variation sum is bounded by M 2^M V. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_le_nat_mul_pow_two_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (hInfluenceLe :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source ≤ 1)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
        D variation M source ≤
      (M : ℝ) * (2 : ℝ) ^ M * V := by
  rw [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum]
  calc
    (Finset.range M).sum
        (fun m =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
            D variation m source) ≤
      (Finset.range M).sum (fun _m => (2 : ℝ) ^ M * V) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmle : m ≤ M := Nat.le_of_lt (Finset.mem_range.mp hm)
        calc
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate
              D variation m source ≤
            (2 : ℝ) ^ m * V :=
              periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_le_pow_two_mul
                D variation hVariationNonneg V hV hVariationLe hInfluenceLe hEdge
                m source
          _ ≤ (2 : ℝ) ^ M * V :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_right₀ (by norm_num) hmle)
              hV
    _ = (M : ℝ) * ((2 : ℝ) ^ M * V) := by
      simp [nsmul_eq_mul]
    _ = (M : ℝ) * (2 : ℝ) ^ M * V := by ring

/-- The normalized finite posterior resolvent obeys the same coarse
M 2^M V upper bound. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_le_nat_mul_pow_two_mul
    {H N : ℕ}
    {hN : 0 < N}
    {beta : ℝ}
    {hbeta : 0 ≤ beta}
    {B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
        H N hN beta hbeta B)
    (variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, 0 ≤ variation e)
    (V : ℝ)
    (hV : 0 ≤ V)
    (hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H, variation e ≤ V)
    (hInfluenceLe :
      ∀ target source : PeriodicHypercubicEvenSpatialSliceLink H,
        D.influence target source ≤ 1)
    (hEdge : 0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H))
    (M : ℕ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        D variation M source ≤
      (M : ℝ) * (2 : ℝ) ^ M * V := by
  let n : ℝ :=
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H)
  let S : ℝ :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum
      D variation M source
  have hnPos : 0 < n := Nat.cast_pos.mpr hEdge
  have hnOne : 1 ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hEdge))
  have hInvLe : n⁻¹ ≤ 1 :=
    (inv_le_one₀ hnPos).2 hnOne
  have hSNonneg : 0 ≤ S := by
    dsimp [S]
    rw [
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_eq_sum]
    exact
      Finset.sum_nonneg fun m _ =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationIterate_nonneg
          D variation hVariationNonneg m source
  have hSBound :
      S ≤ (M : ℝ) * (2 : ℝ) ^ M * V := by
    dsimp [S]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanVariationPartialSum_le_nat_mul_pow_two_mul
        D variation hVariationNonneg V hV hVariationLe hInfluenceLe
        hEdge M source
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
  change n⁻¹ * S ≤ (M : ℝ) * (2 : ℝ) ^ M * V
  calc
    n⁻¹ * S ≤ 1 * S :=
      mul_le_mul_of_nonneg_right hInvLe hSNonneg
    _ = S := one_mul S
    _ ≤ (M : ℝ) * (2 : ℝ) ^ M * V := hSBound

/-- Specialization to the canonical Harnack seed and exact target-local
variation profile. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackSeedRandomScanFiniteResolventProfile_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (M : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
          H N hN beta hbeta B)
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
          beta target)
        M source ≤
      (M : ℝ) * (2 : ℝ) ^ M *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta := by
  let width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  have hWidth : 0 ≤ width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
      beta hbeta
  have hVariationNonneg :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
            beta target e :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation_nonneg
      beta hbeta target
  have hVariationLe :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
            beta target e ≤ width := by
    intro e
    classical
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
    by_cases he : e = target
    · simp [he]
    · simp [he, hWidth]
  have hEdge :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
          simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
        ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩
  simpa [width] using
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile_le_nat_mul_pow_two_mul
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
        H N hN beta hbeta B)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
        beta target)
      hVariationNonneg
      width
      hWidth
      hVariationLe
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData_influence_le_one
        H N hN beta hbeta B)
      hEdge
      M
      source

end

end MathlibAnalytic
end MGAP4D
