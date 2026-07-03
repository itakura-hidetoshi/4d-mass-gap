import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanGreenResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The part of an observable removed by one exact physical-link heat-bath
projection. -/
def FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathResidual
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f : L.Configuration → ℝ) :
    L.Configuration → ℝ :=
  fun A => f A - L.singleLinkHeatBathProjection e f A

/-- A centered link-variation profile bounds the pointwise residual left by one
exact heat-bath projection. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.singleLinkHeatBathResidual_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (e : L.Edge)
    (A : L.Configuration) :
    |L.singleLinkHeatBathResidual e f A| ≤ P.variation e := by
  classical
  have hMass :
      (∑ g : L.Gauge,
        (L.singleLinkConditionalPMF A e g).toReal) = 1 :=
    finite_oriented_pmf_sum_toReal_eq_one
      (L.singleLinkConditionalPMF A e)
  have hRewrite :
      f A -
          ∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g) =
        ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal *
            (f A - f (L.replaceLink A e g)) := by
    calc
      f A -
          ∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g) =
        1 * f A -
          ∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g) := by ring
      _ = (∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal) * f A -
          ∑ g : L.Gauge,
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g) := by rw [hMass]
      _ = ∑ g : L.Gauge,
          ((L.singleLinkConditionalPMF A e g).toReal * f A -
            (L.singleLinkConditionalPMF A e g).toReal *
              f (L.replaceLink A e g)) := by
        rw [Finset.sum_mul, Finset.sum_sub_distrib]
      _ = ∑ g : L.Gauge,
          (L.singleLinkConditionalPMF A e g).toReal *
            (f A - f (L.replaceLink A e g)) := by
        apply Finset.sum_congr rfl
        intro g _hg
        ring
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathResidual
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  rw [hRewrite]
  apply finite_pmf_abs_expectation_le_bound
  intro g
  apply P.variation_bound e A (L.replaceLink A e g)
  intro e' hne
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hne]

/-- Local right-subtraction linearity used by the covariance-decrement layer. -/
private theorem covarianceDecrement_gibbsPairing_sub_right
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

/-- Local left-subtraction linearity used by the covariance-decrement layer. -/
private theorem covarianceDecrement_gibbsPairing_sub_left
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g h : L.Configuration → ℝ) :
    L.gibbsPairingReal (fun A => f A - g A) h =
      L.gibbsPairingReal f h - L.gibbsPairingReal g h := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Local scalar linearity used by the covariance-decrement layer. -/
private theorem covarianceDecrement_gibbsPairing_const_mul_right
    (L : FiniteOrientedLatticeWilsonSystem)
    (f g : L.Configuration → ℝ)
    (c : ℝ) :
    L.gibbsPairingReal f (fun A => c * g A) =
      c * L.gibbsPairingReal f g := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Local finite-sum linearity used by the covariance-decrement layer. -/
private theorem covarianceDecrement_gibbsPairing_fintype_sum_right
    (L : FiniteOrientedLatticeWilsonSystem)
    {ι : Type*} [Fintype ι]
    (f : L.Configuration → ℝ)
    (g : ι → L.Configuration → ℝ) :
    L.gibbsPairingReal f (fun A => ∑ i : ι, g i A) =
      ∑ i : ι, L.gibbsPairingReal f (g i) := by
  classical
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
  calc
    (∑ A : L.Configuration,
      L.gibbsProbabilityReal A * f A * ∑ i : ι, g i A) =
        ∑ A : L.Configuration,
          ∑ i : ι,
            L.gibbsProbabilityReal A * f A * g i A := by
      apply Finset.sum_congr rfl
      intro A _hA
      rw [Finset.mul_sum]
    _ = ∑ i : ι,
        ∑ A : L.Configuration,
          L.gibbsProbabilityReal A * f A * g i A := by
      rw [Finset.sum_comm]

/-- The range of a one-link heat-bath projection is Gibbs-orthogonal to the
residual removed by that same projection. -/
theorem finite_oriented_singleLinkHeatBathProjection_pairing_residual_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjection e f)
        (L.singleLinkHeatBathResidual e g) = 0 := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathResidual
  rw [covarianceDecrement_gibbsPairing_sub_right]
  have hProjection :=
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
      L e (L.singleLinkHeatBathProjection e f) g
  rw [finite_oriented_singleLinkHeatBathProjection_idempotent] at hProjection
  exact sub_eq_zero.mpr hProjection

/-- The Gibbs pairing with a one-link residual may be projected to residuals in
both arguments. -/
theorem finite_oriented_singleLinkHeatBathResidual_pairing_identity
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f (L.singleLinkHeatBathResidual e g) =
      L.gibbsPairingReal
        (L.singleLinkHeatBathResidual e f)
        (L.singleLinkHeatBathResidual e g) := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathResidual
  rw [covarianceDecrement_gibbsPairing_sub_left]
  have hZero :=
    finite_oriented_singleLinkHeatBathProjection_pairing_residual_eq_zero
      L e f g
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathResidual at hZero
  rw [hZero]
  ring

/-- The Gibbs pairing of two one-link heat-bath residuals is bounded by the
product of their linkwise variations. -/
theorem finite_oriented_singleLinkHeatBathResidual_pairing_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (e : L.Edge) :
    |L.gibbsPairingReal
        (L.singleLinkHeatBathResidual e f)
        (L.singleLinkHeatBathResidual e g)| ≤
      P.variation e * Q.variation e := by
  classical
  letI : Fintype L.Configuration := Fintype.ofFinite L.Configuration
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  calc
    |∑ A : L.Configuration,
        (L.gibbsPMF A).toReal * L.singleLinkHeatBathResidual e f A *
          L.singleLinkHeatBathResidual e g A| =
      |∑ A : L.Configuration,
        (L.gibbsPMF A).toReal *
          (L.singleLinkHeatBathResidual e f A *
            L.singleLinkHeatBathResidual e g A)| := by
      congr 1
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ ≤ P.variation e * Q.variation e := by
      apply finite_pmf_abs_expectation_le_bound
      intro A
      rw [abs_mul]
      exact mul_le_mul
        (P.singleLinkHeatBathResidual_abs_le e A)
        (Q.singleLinkHeatBathResidual_abs_le e A)
        (abs_nonneg _)
        (P.variation_nonneg e)

/-- The difference between an observable and its uniform random-scan average is
the average of its one-link heat-bath residuals. -/
theorem finite_oriented_sub_randomScanConditionalAverage_eq_residual_average
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (g : L.Configuration → ℝ) :
    (fun A => g A - L.randomScanConditionalAverage g A) =
      fun A => (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge, L.singleLinkHeatBathResidual e g A := by
  classical
  have hCardNe : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  funext A
  change
    g A - (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ target : L.Edge,
          L.singleLinkConditionalExpectation g A target =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          (g A - L.singleLinkConditionalExpectation g A e)
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hCardNe]

/-- The one-step random-scan Gibbs-pairing decrement is the uniform average of
single-link residual pairings. -/
theorem finite_oriented_randomScan_gibbsPairing_decrement_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g -
        L.gibbsPairingReal f (L.randomScanConditionalAverage g) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          L.gibbsPairingReal
            (L.singleLinkHeatBathResidual e f)
            (L.singleLinkHeatBathResidual e g) := by
  rw [← covarianceDecrement_gibbsPairing_sub_right]
  rw [finite_oriented_sub_randomScanConditionalAverage_eq_residual_average
    L hEdge g]
  rw [covarianceDecrement_gibbsPairing_const_mul_right]
  rw [covarianceDecrement_gibbsPairing_fintype_sum_right]
  apply congrArg (fun x => (Fintype.card L.Edge : ℝ)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro e _he
  exact finite_oriented_singleLinkHeatBathResidual_pairing_identity L e f g

/-- Centered variation profiles bound one uniform random-scan Gibbs-pairing
decrement by the diagonal product of their current link variations. -/
theorem finite_oriented_randomScan_gibbsPairing_decrement_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (hEdge : 0 < Fintype.card L.Edge) :
    |L.gibbsPairingReal f g -
        L.gibbsPairingReal f (L.randomScanConditionalAverage g)| ≤
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge, P.variation e * Q.variation e := by
  rw [finite_oriented_randomScan_gibbsPairing_decrement_eq L hEdge f g]
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  apply mul_le_mul_of_nonneg_left _
    (inv_nonneg.mpr (Nat.cast_nonneg _))
  calc
    |∑ e : L.Edge,
        L.gibbsPairingReal
          (L.singleLinkHeatBathResidual e f)
          (L.singleLinkHeatBathResidual e g)| ≤
      ∑ e : L.Edge,
        |L.gibbsPairingReal
          (L.singleLinkHeatBathResidual e f)
          (L.singleLinkHeatBathResidual e g)| :=
      finite_abs_sum_le_sum_abs Finset.univ _
    _ ≤ ∑ e : L.Edge, P.variation e * Q.variation e := by
      apply Finset.sum_le_sum
      intro e _he
      exact finite_oriented_singleLinkHeatBathResidual_pairing_abs_le P Q e

end

end MathlibAnalytic
end MGAP4D
