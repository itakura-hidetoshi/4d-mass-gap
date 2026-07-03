import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonRandomScanGreenResolvent
import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonRandomScanHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A centered link-variation profile bounds the pointwise fluctuation left by
one exact heat-bath projection. -/
theorem
    FiniteOrientedLatticeWilsonCenteredVariationProfile.singleLinkHeatBathFluctuation_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (e : L.Edge)
    (A : L.Configuration) :
    |L.singleLinkHeatBathFluctuation e f A| ≤ P.variation e := by
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
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuation
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
    FiniteOrientedLatticeWilsonSystem.singleLinkConditionalExpectation
  rw [hRewrite]
  apply finite_pmf_abs_expectation_le_bound
  intro g
  apply P.variation_bound e A (L.replaceLink A e g)
  intro e' hne
  simp [FiniteOrientedLatticeWilsonSystem.replaceLink, hne]

/-- The range of a one-link heat-bath projection is Gibbs-orthogonal to the
fluctuation removed by that same projection. -/
theorem finite_oriented_singleLinkHeatBathProjection_pairing_fluctuation_eq_zero
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal
        (L.singleLinkHeatBathProjection e f)
        (L.singleLinkHeatBathFluctuation e g) = 0 := by
  unfold FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuation
  rw [finite_oriented_gibbsPairingReal_sub_right]
  have hProjection :=
    finite_oriented_singleLinkHeatBath_gibbsPairing_projection_symm
      L e (L.singleLinkHeatBathProjection e f) g
  rw [finite_oriented_singleLinkHeatBathProjection_idempotent] at hProjection
  exact sub_eq_zero.mpr hProjection

/-- The Gibbs pairing with a one-link fluctuation may be projected to
fluctuations in both arguments. -/
theorem finite_oriented_singleLinkHeatBathFluctuation_pairing_identity
    (L : FiniteOrientedLatticeWilsonSystem)
    (e : L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f (L.singleLinkHeatBathFluctuation e g) =
      L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuation e f)
        (L.singleLinkHeatBathFluctuation e g) := by
  change
    L.gibbsPairingReal f (L.singleLinkHeatBathFluctuation e g) =
      L.gibbsPairingReal
        (f - L.singleLinkHeatBathProjection e f)
        (L.singleLinkHeatBathFluctuation e g)
  rw [finite_oriented_gibbsPairingReal_sub_left]
  rw [finite_oriented_singleLinkHeatBathProjection_pairing_fluctuation_eq_zero]
  ring

/-- The Gibbs pairing of two one-link heat-bath fluctuations is bounded by the
product of their linkwise variations. -/
theorem finite_oriented_singleLinkHeatBathFluctuation_pairing_abs_le
    {L : FiniteOrientedLatticeWilsonSystem}
    {f g : L.Configuration → ℝ}
    (P : FiniteOrientedLatticeWilsonCenteredVariationProfile L f)
    (Q : FiniteOrientedLatticeWilsonCenteredVariationProfile L g)
    (e : L.Edge) :
    |L.gibbsPairingReal
        (L.singleLinkHeatBathFluctuation e f)
        (L.singleLinkHeatBathFluctuation e g)| ≤
      P.variation e * Q.variation e := by
  unfold FiniteOrientedLatticeWilsonSystem.gibbsPairingReal
    FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal
  apply finite_pmf_abs_expectation_le_bound
  intro A
  rw [abs_mul]
  exact mul_le_mul
    (P.singleLinkHeatBathFluctuation_abs_le e A)
    (Q.singleLinkHeatBathFluctuation_abs_le e A)
    (abs_nonneg _)
    (P.variation_nonneg e)

/-- The difference between an observable and its uniform random-scan average is
the average of its one-link heat-bath fluctuations. -/
theorem finite_oriented_sub_randomScanConditionalAverage_eq_fluctuation_average
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (g : L.Configuration → ℝ) :
    g - L.randomScanConditionalAverage g =
      fun A => (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge, L.singleLinkHeatBathFluctuation e g A := by
  classical
  have hCardNe : (Fintype.card L.Edge : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hEdge)
  funext A
  unfold FiniteOrientedLatticeWilsonSystem.randomScanConditionalAverage
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathFluctuation
    FiniteOrientedLatticeWilsonSystem.singleLinkHeatBathProjection
  simp only [Pi.sub_apply]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [hCardNe]
  ring

/-- The one-step random-scan Gibbs-pairing decrement is the uniform average of
single-link fluctuation pairings. -/
theorem finite_oriented_randomScan_gibbsPairing_decrement_eq
    (L : FiniteOrientedLatticeWilsonSystem)
    (hEdge : 0 < Fintype.card L.Edge)
    (f g : L.Configuration → ℝ) :
    L.gibbsPairingReal f g -
        L.gibbsPairingReal f (L.randomScanConditionalAverage g) =
      (Fintype.card L.Edge : ℝ)⁻¹ *
        ∑ e : L.Edge,
          L.gibbsPairingReal
            (L.singleLinkHeatBathFluctuation e f)
            (L.singleLinkHeatBathFluctuation e g) := by
  rw [← finite_oriented_gibbsPairingReal_sub_right]
  rw [finite_oriented_sub_randomScanConditionalAverage_eq_fluctuation_average
    L hEdge g]
  rw [finite_oriented_gibbsPairingReal_const_mul_right]
  apply congrArg (fun x => (Fintype.card L.Edge : ℝ)⁻¹ * x)
  have hSumFunction :
      (fun A : L.Configuration =>
        ∑ e : L.Edge, L.singleLinkHeatBathFluctuation e g A) =
        ∑ e : L.Edge, L.singleLinkHeatBathFluctuation e g := by
    funext A
    simp
  rw [hSumFunction,
    finite_oriented_gibbsPairingReal_finset_sum_right]
  apply Finset.sum_congr rfl
  intro e _he
  exact finite_oriented_singleLinkHeatBathFluctuation_pairing_identity L e f g

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
          (L.singleLinkHeatBathFluctuation e f)
          (L.singleLinkHeatBathFluctuation e g)| ≤
      ∑ e : L.Edge,
        |L.gibbsPairingReal
          (L.singleLinkHeatBathFluctuation e f)
          (L.singleLinkHeatBathFluctuation e g)| :=
      finite_abs_sum_le_sum_abs Finset.univ _
    _ ≤ ∑ e : L.Edge, P.variation e * Q.variation e := by
      apply Finset.sum_le_sum
      intro e _he
      exact finite_oriented_singleLinkHeatBathFluctuation_pairing_abs_le P Q e

end

end MathlibAnalytic
end MGAP4D
