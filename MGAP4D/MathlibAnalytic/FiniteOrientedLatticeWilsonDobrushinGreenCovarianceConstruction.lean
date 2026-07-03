import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanGreenResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The conditional-average notation used by the variation chain is the native
one-link heat-bath projection. -/
theorem finite_oriented_singleLinkConditionalAverage_eq_projection
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (target : L.Edge) :
    (fun A => L.singleLinkConditionalAverage f A target) =
      L.singleLinkHeatBathProjection target f := by
  rfl

/-- A link-variation certificate controls the displacement from an observable
to its exact one-link conditional average. -/
theorem
    FiniteOrientedLatticeWilsonLinkVariationBound.abs_sub_singleLinkConditionalAverage_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonLinkVariationBound L f)
    (A : L.Configuration)
    (target : L.Edge) :
    |f A - L.singleLinkConditionalAverage f A target| ≤
      P.variation target := by
  classical
  have hMass :
      (∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A target g).toReal) = 1 :=
    finite_oriented_pmf_sum_toReal_eq_one
      (L.singleLinkConditionalPMF A target)
  have hRewrite :
      f A - L.singleLinkConditionalAverage f A target =
        ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A target g).toReal *
            (f A - f (L.replaceLink A target g)) := by
    unfold FiniteOrientedLatticeWilsonSystem.singleLinkConditionalAverage
    calc
      f A - ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A target g).toReal *
            f (L.replaceLink A target g) =
        (∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A target g).toReal) * f A -
            ∑ g : L.Gauge,
              (L.singleLinkConditionalPMF A target g).toReal *
                f (L.replaceLink A target g) := by
          rw [hMass]
          ring
      _ = ∑ g : L.Gauge,
          ((L.singleLinkConditionalPMF A target g).toReal * f A -
            (L.singleLinkConditionalPMF A target g).toReal *
              f (L.replaceLink A target g)) := by
          rw [Finset.sum_mul, Finset.sum_sub_distrib]
      _ = ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A target g).toReal *
            (f A - f (L.replaceLink A target g)) := by
          apply Finset.sum_congr rfl
          intro g _hg
          ring
  rw [hRewrite]
  apply finite_pmf_abs_expectation_le_bound
  intro g
  exact P.variation_bound target A (L.replaceLink A target g) (by
    intro source hSource
    simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hSource])

private theorem finite_oriented_gibbsPairingReal_sub_left
    (L : FiniteOrientedLatticeWilsonSystem)
    (f h g : L.Configuration → ℝ) :
    L.gibbsPairingReal (fun A => f A - h A) g =
      L.gibbsPairingReal f g - L.gibbsPairingReal h g := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

private theorem finite_oriented_gibbsPairingReal_sub_right
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

/-- The one-link fluctuation is Gibbs-orthogonal to the corresponding
conditional-expectation range. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_residual_projection_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (fun A => f A - L.singleLinkHeatBathProjection target f A)
        (L.singleLinkHeatBathProjection target g) = 0 := by
  have hSymm :=
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
      L target f g
  have hIdemSymm :=
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
      L target (L.singleLinkHeatBathProjection target f) g
  rw [finite_oriented_singleLinkHeatBathProjection_idempotent] at hIdemSymm
  rw [finite_oriented_gibbsPairingReal_sub_left]
  rw [← hSymm, hIdemSymm, sub_self]

/-- Pairing a one-link fluctuation against an arbitrary observable only sees
the corresponding fluctuation of that observable. -/
theorem finite_oriented_singleLinkHeatBath_gibbsPairing_residual_eq_residual
    (L : FiniteOrientedLatticeWilsonSystem)
    (target : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (fun A => f A - L.singleLinkHeatBathProjection target f A) g =
      L.gibbsPairingReal
        (fun A => f A - L.singleLinkHeatBathProjection target f A)
        (fun A => g A - L.singleLinkHeatBathProjection target g A) := by
  rw [finite_oriented_gibbsPairingReal_sub_right]
  rw [finite_oriented_singleLinkHeatBath_gibbsPairing_residual_projection_zero]
  ring

/-- The Gibbs pairing contribution removed by one exact link update is bounded
by the product of the two link variations at that link. -/
theorem finite_oriented_singleLinkConditionalAverage_gibbsPairing_residual_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (target : L.Edge) :
    |L.gibbsPairingReal
        (fun A => f A - L.singleLinkConditionalAverage f A target) g| ≤
      P.variation target * Q.variation target := by
  classical
  change
    |L.gibbsPairingReal
        (fun A => f A - L.singleLinkHeatBathProjection target f A) g| ≤ _
  rw [finite_oriented_singleLinkHeatBath_gibbsPairing_residual_eq_residual]
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  calc
    |∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          (f A - L.singleLinkHeatBathProjection target f A) *
          (g A - L.singleLinkHeatBathProjection target g A)| ≤
      ∑ A : L.Configuration,
        |L.gibbsProbabilityReal A *
          (f A - L.singleLinkHeatBathProjection target f A) *
          (g A - L.singleLinkHeatBathProjection target g A)| :=
      finite_abs_sum_le_sum_abs Finset.univ _
    _ = ∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          |f A - L.singleLinkHeatBathProjection target f A| *
          |g A - L.singleLinkHeatBathProjection target g A| := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [abs_mul, abs_mul,
        abs_of_nonneg (finite_oriented_gibbsProbabilityReal_nonneg L A)]
    _ ≤ ∑ A : L.Configuration,
        L.gibbsProbabilityReal A * P.variation target *
          Q.variation target := by
      apply Finset.sum_le_sum
      intro A _hA
      have hP :
          |f A - L.singleLinkHeatBathProjection target f A| ≤
            P.variation target := by
        change |f A - L.singleLinkConditionalAverage f A target| ≤ _
        exact P.toFiniteOrientedLatticeWilsonLinkVariationBound
          |>.abs_sub_singleLinkConditionalAverage_le A target
      have hQ :
          |g A - L.singleLinkHeatBathProjection target g A| ≤
            Q.variation target := by
        change |g A - L.singleLinkConditionalAverage g A target| ≤ _
        exact Q.toFiniteOrientedLatticeWilsonLinkVariationBound
          |>.abs_sub_singleLinkConditionalAverage_le A target
      have hFirst :
          L.gibbsProbabilityReal A *
              |f A - L.singleLinkHeatBathProjection target f A| ≤
            L.gibbsProbabilityReal A * P.variation target :=
        mul_le_mul_of_nonneg_left hP
          (finite_oriented_gibbsProbabilityReal_nonneg L A)
      calc
        L.gibbsProbabilityReal A *
            |f A - L.singleLinkHeatBathProjection target f A| *
            |g A - L.singleLinkHeatBathProjection target g A| ≤
          L.gibbsProbabilityReal A * P.variation target *
            |g A - L.singleLinkHeatBathProjection target g A| :=
          mul_le_mul_of_nonneg_right hFirst (abs_nonneg _)
        _ ≤ L.gibbsProbabilityReal A * P.variation target *
            Q.variation target :=
          mul_le_mul_of_nonneg_left hQ
            (mul_nonneg
              (finite_oriented_gibbsProbabilityReal_nonneg L A)
              (P.variation_nonneg target))
    _ = P.variation target * Q.variation target := by
      have hMass :
          (∑ A : L.Configuration, L.gibbsProbabilityReal A) = 1 := by
        simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
          (finite_pmf_sum_toReal_eq_one L.gibbsPMF)
      calc
        (∑ A : L.Configuration,
          L.gibbsProbabilityReal A * P.variation target *
            Q.variation target) =
          (∑ A : L.Configuration, L.gibbsProbabilityReal A) *
            (P.variation target * Q.variation target) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro A _hA
              ring
        _ = P.variation target * Q.variation target := by
          rw [hMass]
          ring

private theorem finite_oriented_randomScan_residual_pointwise
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (hEdge : 0 < Fintype.card L.Edge)
    (A : L.Configuration) :
    f A - L.randomScanConditionalAverage f A =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          (f A - L.singleLinkConditionalAverage f A target) := by
  classical
  have hCardNe : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  unfold FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hCardNe]
  ring

/-- The Gibbs pairing decrement of one uniform random-scan step is bounded by
the normalized sum of linkwise variation products. -/
theorem finite_oriented_randomScanConditionalAverage_gibbsPairing_residual_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (hEdge : 0 < Fintype.card L.Edge) :
    |L.gibbsPairingReal
        (fun A => f A - L.randomScanConditionalAverage f A) g| ≤
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          P.variation target * Q.variation target := by
  classical
  have hInvNonneg : 0 ≤ (Fintype.card L.Edge : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hPairingEq :
      L.gibbsPairingReal
          (fun A => f A - L.randomScanConditionalAverage f A) g =
        (Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ target : L.Edge,
            L.gibbsPairingReal
              (fun A => f A - L.singleLinkConditionalAverage f A target) g := by
    unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    calc
      (∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          (f A - L.randomScanConditionalAverage f A) * g A) =
        ∑ A : L.Configuration,
          (Fintype.card L.Edge : ℝ)⁻¹ *
            ∑ target : L.Edge,
              (L.gibbsProbabilityReal A *
                (f A - L.singleLinkConditionalAverage f A target) * g A) := by
          apply Finset.sum_congr rfl
          intro A _hA
          rw [finite_oriented_randomScan_residual_pointwise L f hEdge A]
          rw [Finset.mul_sum]
          apply congrArg
          apply Finset.sum_congr rfl
          intro target _hTarget
          ring
      _ = (Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ A : L.Configuration,
            ∑ target : L.Edge,
              (L.gibbsProbabilityReal A *
                (f A - L.singleLinkConditionalAverage f A target) * g A) := by
          rw [Finset.mul_sum]
      _ = (Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ target : L.Edge,
            ∑ A : L.Configuration,
              (L.gibbsProbabilityReal A *
                (f A - L.singleLinkConditionalAverage f A target) * g A) := by
          rw [Finset.sum_comm]
      _ = (Fintype.card L.Edge : ℝ)⁻¹ *
          ∑ target : L.Edge,
            L.gibbsPairingReal
              (fun A => f A - L.singleLinkConditionalAverage f A target) g := by
          rfl
  rw [hPairingEq, abs_mul, abs_of_nonneg hInvNonneg]
  apply mul_le_mul_of_nonneg_left _ hInvNonneg
  calc
    |∑ target : L.Edge,
        L.gibbsPairingReal
          (fun A => f A - L.singleLinkConditionalAverage f A target) g| ≤
      ∑ target : L.Edge,
        |L.gibbsPairingReal
          (fun A => f A - L.singleLinkConditionalAverage f A target) g| :=
      finite_abs_sum_le_sum_abs Finset.univ _
    _ ≤ ∑ target : L.Edge,
        P.variation target * Q.variation target := by
      apply Finset.sum_le_sum
      intro target _hTarget
      exact finite_oriented_singleLinkConditionalAverage_gibbsPairing_residual_abs_le
        P Q target

/-- Subtracting a constant preserves a centered link-variation profile. -/
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

/-- One random-scan step changes static Gibbs covariance by at most the
normalized linkwise variation pairing. -/
theorem finite_oriented_gibbsCovarianceReal_sub_randomScan_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (hEdge : 0 < Fintype.card L.Edge) :
    |L.gibbsCovarianceReal f g -
        L.gibbsCovarianceReal (L.randomScanConditionalAverage f) g| ≤
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          P.variation target * Q.variation target := by
  have hExpectation :=
    finite_oriented_randomScanConditionalAverage_gibbsExpectationReal
      L f hEdge
  have hDifference :
      L.gibbsCovarianceReal f g -
          L.gibbsCovarianceReal (L.randomScanConditionalAverage f) g =
        L.gibbsPairingReal
          (fun A => f A - L.randomScanConditionalAverage f A)
          (fun A => g A - L.gibbsExpectationReal g) := by
    classical
    unfold FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
    rw [hExpectation]
    unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro A _hA
    ring
  rw [hDifference]
  simpa using
    finite_oriented_randomScanConditionalAverage_gibbsPairing_residual_abs_le
      P (Q.subConst (L.gibbsExpectationReal g)) hEdge

/-- The covariance decrement between consecutive random-scan iterates obeys
the same linkwise bound with the iterated variation profile. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.gibbsCovarianceReal_iterate_sub_succ_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (k : ℕ) :
    |L.gibbsCovarianceReal
        (L.randomScanConditionalAverageIterate f k) g -
      L.gibbsCovarianceReal
        (L.randomScanConditionalAverageIterate f (k + 1)) g| ≤
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ source : L.Edge,
          P.randomScanConditionalAverageVariationIterate D k source *
            Q.variation source := by
  simpa only [
    finite_oriented_randomScanConditionalAverageIterate_succ,
    FiniteOrientedLatticeWilsonCenteredVariationProfile.randomScanConditionalAverageVariationIterate]
    using finite_oriented_gibbsCovarianceReal_sub_randomScan_abs_le
      (P.randomScanConditionalAverageCenteredVariationIterate D k)
      Q hEdge

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
              |a n - a (n + 1)| := add_le_add_right ih _

private theorem finite_oriented_weightedInfluenceGreen_sum_mul_eq
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

/-- Every finite random-scan covariance telescope is dominated by the full
Dobrushin Green kernel. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.gibbsCovarianceReal_sub_iterate_abs_le_green
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (D : FiniteOrientedLatticeWilsonDobrushinMatrixData L)
    (hEdge : 0 < Fintype.card L.Edge)
    (n : ℕ) :
    |L.gibbsCovarianceReal f g -
      L.gibbsCovarianceReal
        (L.randomScanConditionalAverageIterate f n) g| ≤
      ∑ target : L.Edge,
        ∑ source : L.Edge,
          P.variation target * D.influenceGreenTail 0 target source *
            Q.variation source := by
  classical
  let covariance : ℕ → ℝ := fun k =>
    L.gibbsCovarianceReal
      (L.randomScanConditionalAverageIterate f k) g
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
    exact P.gibbsCovarianceReal_iterate_sub_succ_abs_le Q D hEdge k
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
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  calc
    |L.gibbsCovarianceReal f g -
      L.gibbsCovarianceReal
        (L.randomScanConditionalAverageIterate f n) g| =
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
      finite_oriented_weightedInfluenceGreen_sum_mul_eq D P.variation Q.variation

end

end MathlibAnalytic
end MGAP4D
