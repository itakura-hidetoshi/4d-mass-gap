import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanCovarianceDecrement
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Subtracting a constant preserves every link variation and its centered
fiber-radius certificate. -/
noncomputable def
    FiniteOrientedLatticeWilsonCenteredVariationProfile.subConst
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (c : ℝ) :
    FiniteOrientedLatticeWilsonCenteredVariationProfile L
      (fun A => f A - c) :=
  { variation := P.variation
    variation_nonneg := P.variation_nonneg
    variation_bound := by
      intro target A B hAgree
      simpa only [sub_sub_sub_cancel_right] using
        P.variation_bound target A B hAgree
    fiberCenter := fun A target => P.fiberCenter A target - c
    fiber_radius_bound := by
      intro A target g
      simpa only [sub_sub_sub_cancel_right] using
        P.fiber_radius_bound A target g }

@[simp] theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.subConst_variation
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (c : ℝ)
    (target : L.Edge) :
    (P.subConst c).variation target = P.variation target := rfl

private theorem greenCovarianceTelescope_gibbsPairing_sub_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal f (fun A => g A - h A) =
      L.gibbsPairingReal f g - L.gibbsPairingReal f h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Time zero of the stationary random-scan covariance is the static Gibbs
covariance, with the observable order inherited from the temporal definition. -/
@[simp] theorem finite_oriented_randomScanTemporalCovarianceReal_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.randomScanTemporalCovarianceReal f g 0 =
      L.gibbsCovarianceReal f g := by
  rfl

/-- Static Gibbs covariance is symmetric. -/
theorem finite_oriented_gibbsCovarianceReal_symm
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ) :
    L.gibbsCovarianceReal f g = L.gibbsCovarianceReal g f := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
    FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Consecutive stationary temporal covariances differ by one random-scan
Dirichlet decrement.  The iterated profile belongs to the advanced observable,
while the fixed observable keeps its initial variation profile. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanTemporalCovarianceReal_sub_succ_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (k : ℕ) :
    |L.randomScanTemporalCovarianceReal g f k -
      L.randomScanTemporalCovarianceReal g f (k + 1)| ≤
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ source : L.Edge,
          P.randomScanConditionalAverageVariationIterate D k source *
            Q.variation source := by
  let centeredG : L.Configuration → ℝ :=
    fun A => g A - L.gibbsExpectationReal g
  let iterateF : L.Configuration → ℝ :=
    L.randomScanConditionalAverageIterate f k
  have hDecrement :=
    finite_oriented_randomScan_gibbsPairing_decrement_abs_le
      (Q.subConst (L.gibbsExpectationReal g))
      (P.randomScanConditionalAverageCenteredVariationIterate D k)
      hEdge
  have hIdentity :
      L.randomScanTemporalCovarianceReal g f k -
          L.randomScanTemporalCovarianceReal g f (k + 1) =
        L.gibbsPairingReal centeredG iterateF -
          L.gibbsPairingReal centeredG
            (L.randomScanConditionalAverage iterateF) := by
    unfold FiniteOrientedLatticeWilsonSystem.randomScanTemporalCovarianceReal
    rw [finite_oriented_randomScanConditionalAverageIterate_succ]
    change
      L.gibbsPairingReal centeredG
          (fun A => iterateF A - L.gibbsExpectationReal f) -
        L.gibbsPairingReal centeredG
          (fun A => L.randomScanConditionalAverage iterateF A -
            L.gibbsExpectationReal f) = _
    rw [greenCovarianceTelescope_gibbsPairing_sub_right,
      greenCovarianceTelescope_gibbsPairing_sub_right]
    ring
  rw [hIdentity]
  simpa only [
    FiniteOrientedLatticeWilsonCenteredVariationProfile.subConst_variation,
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate,
    mul_comm] using hDecrement

private theorem abs_sub_nat_le_sum_range_abs_sub_succ
    (a : ℕ → ℝ)
    (n : ℕ) :
    |a 0 - a n| ≤
      ∑ k ∈ Finset.range n, |a k - a (k + 1)| := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        |a 0 - a (n + 1)| =
            |(a 0 - a n) + (a n - a (n + 1))| := by
              congr 1
              ring
        _ ≤ |a 0 - a n| + |a n - a (n + 1)| := abs_add_le _ _
        _ ≤ (∑ k ∈ Finset.range n, |a k - a (k + 1)|) +
              |a n - a (n + 1)| := add_le_add ih (le_refl _)

private theorem finite_oriented_weightedInfluenceGreen_mul_sum_eq
    {L : FiniteOrientedLatticeWilsonSystem}
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (u v : L.Edge → ℝ) :
    (∑ source : L.Edge,
      D.weightedInfluenceGreen u source * v source) =
      ∑ target : L.Edge,
        ∑ source : L.Edge,
          u target * D.influenceGreenTail 0 target source * v source := by
  classical
  unfold FiniteOrientedLatticeWilsonDobrushinMatrixData.weightedInfluenceGreen
  calc
    (∑ source : L.Edge,
      (∑ target : L.Edge,
        u target * D.influenceGreenTail 0 target source) * v source) =
      ∑ source : L.Edge,
        ∑ target : L.Edge,
          u target * D.influenceGreenTail 0 target source * v source := by
            apply Finset.sum_congr rfl
            intro source _hSource
            rw [Finset.sum_mul]
    _ = ∑ target : L.Edge,
        ∑ source : L.Edge,
          u target * D.influenceGreenTail 0 target source * v source := by
            rw [Finset.sum_comm]

/-- Every finite stationary covariance telescope is dominated by the full
Dobrushin Green kernel.  This is the finite-time core of the static covariance
comparison; no limiting argument is used in this theorem. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanTemporalCovarianceReal_zero_sub_abs_le_green
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (n : ℕ) :
    |L.randomScanTemporalCovarianceReal g f 0 -
      L.randomScanTemporalCovarianceReal g f n| ≤
      ∑ target : L.Edge,
        ∑ source : L.Edge,
          P.variation target * D.influenceGreenTail 0 target source *
            Q.variation source := by
  classical
  let covariance : ℕ → ℝ := fun k =>
    L.randomScanTemporalCovarianceReal g f k
  have hTelescope :
      |covariance 0 - covariance n| ≤
        ∑ k ∈ Finset.range n,
          |covariance k - covariance (k + 1)| :=
    abs_sub_nat_le_sum_range_abs_sub_succ covariance n
  have hStep :
      ∀ k : ℕ,
        |covariance k - covariance (k + 1)| ≤
          (Fintype.card L.Edge : ℝ)⁻¹ *
            ∑ source : L.Edge,
              P.randomScanConditionalAverageVariationIterate D k source *
                Q.variation source := by
    intro k
    exact P.randomScanTemporalCovarianceReal_sub_succ_abs_le
      Q D hEdge k
  have hStepSum :
      (∑ k ∈ Finset.range n,
        |covariance k - covariance (k + 1)|) ≤
      ∑ k ∈ Finset.range n,
        ((Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ source : L.Edge,
            P.randomScanConditionalAverageVariationIterate D k source *
              Q.variation source) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hStep k
  have hCardNe : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  have hInvNonneg : 0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hNormalized : ∀ source : L.Edge,
      (Fintype.card L.Edge : ℝ)⁻¹ *
          (∑ k ∈ Finset.range n,
            P.randomScanConditionalAverageVariationIterate D k source) ≤
        D.weightedInfluenceGreen P.variation source := by
    intro source
    have hPartial :=
      P.randomScanConditionalAverageVariationIterate_sum_range_le_green
        D hEdge n source
    calc
      (Fintype.card L.Edge : ℝ)⁻¹ *
          (∑ k ∈ Finset.range n,
            P.randomScanConditionalAverageVariationIterate D k source) ≤
        (Fintype.card L.Edge : ℝ)⁻¹ *
          ((Fintype.card L.Edge : ℝ) *
            D.weightedInfluenceGreen P.variation source) :=
          mul_le_mul_of_nonneg_left hPartial hInvNonneg
      _ = D.weightedInfluenceGreen P.variation source := by
        field_simp [hCardNe]
  have hRearrange :
      (∑ k ∈ Finset.range n,
        ((Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ source : L.Edge,
            P.randomScanConditionalAverageVariationIterate D k source *
              Q.variation source)) =
      ∑ source : L.Edge,
        ((Fintype.card L.Edge : ℝ)⁻¹ *
          (∑ k ∈ Finset.range n,
            P.randomScanConditionalAverageVariationIterate D k source)) *
              Q.variation source := by
    calc
      (∑ k ∈ Finset.range n,
        ((Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ source : L.Edge,
            P.randomScanConditionalAverageVariationIterate D k source *
              Q.variation source)) =
        ∑ k ∈ Finset.range n,
          ∑ source : L.Edge,
            (Fintype.card L.Edge : ℝ)⁻¹ *
              (P.randomScanConditionalAverageVariationIterate D k source *
                Q.variation source) := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.mul_sum]
      _ = ∑ source : L.Edge,
          ∑ k ∈ Finset.range n,
            (Fintype.card L.Edge : ℝ)⁻¹ *
              (P.randomScanConditionalAverageVariationIterate D k source *
                Q.variation source) := by
            rw [Finset.sum_comm]
      _ = ∑ source : L.Edge,
          ((Fintype.card L.Edge : ℝ)⁻¹ *
            (∑ k ∈ Finset.range n,
              P.randomScanConditionalAverageVariationIterate D k source)) *
                Q.variation source := by
            apply Finset.sum_congr rfl
            intro source _hSource
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  calc
    |L.randomScanTemporalCovarianceReal g f 0 -
      L.randomScanTemporalCovarianceReal g f n| =
        |covariance 0 - covariance n| := by rfl
    _ ≤ ∑ k ∈ Finset.range n,
        |covariance k - covariance (k + 1)| := hTelescope
    _ ≤ ∑ k ∈ Finset.range n,
        ((Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ source : L.Edge,
            P.randomScanConditionalAverageVariationIterate D k source *
              Q.variation source) := hStepSum
    _ = ∑ source : L.Edge,
        ((Fintype.card L.Edge : ℝ)⁻¹ *
          (∑ k ∈ Finset.range n,
            P.randomScanConditionalAverageVariationIterate D k source)) *
              Q.variation source := hRearrange
    _ ≤ ∑ source : L.Edge,
        D.weightedInfluenceGreen P.variation source *
          Q.variation source := by
      apply Finset.sum_le_sum
      intro source _hSource
      exact mul_le_mul_of_nonneg_right
        (hNormalized source) (Q.variation_nonneg source)
    _ = ∑ target : L.Edge,
        ∑ source : L.Edge,
          P.variation target * D.influenceGreenTail 0 target source *
            Q.variation source :=
      finite_oriented_weightedInfluenceGreen_mul_sum_eq
        D P.variation Q.variation

end

end MathlibAnalytic
end MGAP4D
