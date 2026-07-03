import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicAutomaticL1SpatialCovarianceExplicitExponentialDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The raw periodic plaquette-base `L¹` distance is at most twice the automatic
radius plus three.  The additive three is the exact uniform loss coming from
the two-unit boundary margin, truncated subtraction, and division by two. -/
theorem periodicHypercubicPlaquetteBaseL1Distance_le_two_mul_decayRadius_add_three
    (n : ℕ)
    (source target : PeriodicHypercubicPlaquette n) :
    periodicHypercubicPlaquetteBaseL1Distance n source target ≤
      2 * periodicHypercubicPlaquetteBaseL1DecayRadius n source target + 3 := by
  unfold periodicHypercubicPlaquetteBaseL1DecayRadius
  omega

/-- The automatic-radius exponential is bounded by an exponential in the raw
periodic plaquette-base `L¹` distance.  The floor loss is absorbed exactly into
the prefactor `exp (3 * decayRate / 2)`. -/
theorem
    z2PeriodicHypercubicOriented_exp_neg_decayRate_mul_decayRadius_le_exp_three_halves_mul_exp_neg_half_mul_plaquetteBaseL1Distance
    (n : ℕ)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (source target : PeriodicHypercubicPlaquette n)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    Real.exp
        (-z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
          (periodicHypercubicPlaquetteBaseL1DecayRadius n source target : ℝ)) ≤
      Real.exp
          (3 * z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) *
        Real.exp
          (-(z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) *
            (periodicHypercubicPlaquetteBaseL1Distance n source target : ℝ)) := by
  have hDecayRatePos :
      0 < z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta :=
    z2PeriodicHypercubicOrientedExplicitSpatialDecayRate_pos
      beta hBeta hBetaLt
  have hDistanceNat :=
    periodicHypercubicPlaquetteBaseL1Distance_le_two_mul_decayRadius_add_three
      n source target
  have hDistanceReal :
      (periodicHypercubicPlaquetteBaseL1Distance n source target : ℝ) ≤
        2 *
            (periodicHypercubicPlaquetteBaseL1DecayRadius
              n source target : ℝ) +
          3 := by
    exact_mod_cast hDistanceNat
  have hScaled :
      z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
          (periodicHypercubicPlaquetteBaseL1Distance n source target : ℝ) ≤
        z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
          (2 *
              (periodicHypercubicPlaquetteBaseL1DecayRadius
                n source target : ℝ) +
            3) :=
    mul_le_mul_of_nonneg_left hDistanceReal hDecayRatePos.le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Finite-volume periodic `Z₂` plaquette covariance decay in the standard
exponential form based directly on the raw periodic plaquette-base `L¹`
distance.  The rate is one half of the automatic-radius rate, while the exact
floor loss is retained in the beta-dependent prefactor. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_exp_neg_half_explicitDecayRate_mul_plaquetteBaseL1Distance_of_beta_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
          targetPlaquette)| ≤
      (16 *
          Real.exp
            (3 * z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) /
        (1 - z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) *
        Real.exp
          (-(z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) *
            (periodicHypercubicPlaquetteBaseL1Distance
              n sourcePlaquette targetPlaquette : ℝ)) := by
  have hRateLt :
      z2PeriodicHypercubicOrientedExplicitDobrushinRate beta < 1 :=
    z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_beta_lt
      beta hBetaLt
  have hDenominatorPos :
      0 < 1 - z2PeriodicHypercubicOrientedExplicitDobrushinRate beta :=
    sub_pos.mpr hRateLt
  have hExponentialBound :=
    z2PeriodicHypercubicOriented_exp_neg_decayRate_mul_decayRadius_le_exp_three_halves_mul_exp_neg_half_mul_plaquetteBaseL1Distance
      n beta hBeta sourcePlaquette targetPlaquette hBetaLt
  calc
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
          targetPlaquette)| ≤
      16 *
        (Real.exp
            (-z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
              (periodicHypercubicPlaquetteBaseL1DecayRadius
                n sourcePlaquette targetPlaquette : ℝ)) /
          (1 - z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) :=
      z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_exp_neg_explicitDecayRate_automaticL1_of_beta_lt
        n hn beta hBeta sourcePlaquette targetPlaquette hBetaLt
    _ ≤
      16 *
        ((Real.exp
              (3 *
                  z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta /
                2) *
            Real.exp
              (-(z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) *
                (periodicHypercubicPlaquetteBaseL1Distance
                  n sourcePlaquette targetPlaquette : ℝ))) /
          (1 - z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) := by
      apply mul_le_mul_of_nonneg_left
      · apply (div_le_div_iff₀ hDenominatorPos hDenominatorPos).2
        exact mul_le_mul_of_nonneg_right hExponentialBound hDenominatorPos.le
      · norm_num
    _ =
      (16 *
          Real.exp
            (3 * z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) /
        (1 - z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) *
        Real.exp
          (-(z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) *
            (periodicHypercubicPlaquetteBaseL1Distance
              n sourcePlaquette targetPlaquette : ℝ)) := by
      ring

end

end MathlibAnalytic
end MGAP4D
