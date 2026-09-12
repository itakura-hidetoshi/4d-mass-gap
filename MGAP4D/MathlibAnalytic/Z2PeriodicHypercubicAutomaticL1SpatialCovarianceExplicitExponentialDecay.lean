import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicAutomaticL1SpatialCovarianceExplicitRate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The beta-dependent exponential decay rate associated with the explicit
periodic oriented `Z₂` Dobrushin majorant.  This is a finite-volume covariance
rate per automatic periodic `L¹` radius, not a physical mass-gap definition. -/
def z2PeriodicHypercubicOrientedExplicitSpatialDecayRate
    (beta : ℝ) : ℝ :=
  -Real.log (z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)

/-- Positive coupling makes the explicit beta-only Dobrushin rate positive. -/
theorem z2PeriodicHypercubicOrientedExplicitDobrushinRate_pos
    (beta : ℝ)
    (hBeta : 0 < beta) :
    0 < z2PeriodicHypercubicOrientedExplicitDobrushinRate beta := by
  have hExpOne : 1 < Real.exp (beta * 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by nlinarith)
  unfold z2PeriodicHypercubicOrientedExplicitDobrushinRate
  exact mul_pos (by norm_num)
    (div_pos (sub_pos.mpr hExpOne) (by positivity))

/-- Under the explicit high-temperature threshold, the spatial decay rate is
strictly positive. -/
theorem z2PeriodicHypercubicOrientedExplicitSpatialDecayRate_pos
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta := by
  unfold z2PeriodicHypercubicOrientedExplicitSpatialDecayRate
  exact neg_pos.mpr
    (Real.log_neg
      (z2PeriodicHypercubicOrientedExplicitDobrushinRate_pos beta hBeta)
      (z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_beta_lt
        beta hBetaLt))

/-- Natural powers of the explicit Dobrushin rate are exactly exponential in
the positive-coupling spatial decay rate. -/
theorem z2PeriodicHypercubicOrientedExplicitDobrushinRate_pow_eq_exp_neg_decayRate_mul
    (beta : ℝ)
    (hBeta : 0 < beta)
    (d : ℕ) :
    z2PeriodicHypercubicOrientedExplicitDobrushinRate beta ^ d =
      Real.exp
        (-z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
          (d : ℝ)) := by
  have hRatePos :
      0 < z2PeriodicHypercubicOrientedExplicitDobrushinRate beta :=
    z2PeriodicHypercubicOrientedExplicitDobrushinRate_pos beta hBeta
  calc
    z2PeriodicHypercubicOrientedExplicitDobrushinRate beta ^ d =
        Real.exp
            (Real.log
              (z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) ^ d := by
      rw [Real.exp_log hRatePos]
    _ = Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
            (d : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      unfold z2PeriodicHypercubicOrientedExplicitSpatialDecayRate
      ring

/-- Automatic finite-volume periodic `Z₂` plaquette covariance decay written
with an explicit positive exponential rate. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_exp_neg_explicitDecayRate_automaticL1_of_beta_lt
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
      16 *
        (Real.exp
            (-z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
              (periodicHypercubicPlaquetteBaseL1DecayRadius
                n sourcePlaquette targetPlaquette : ℝ)) /
          (1 -
            z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) := by
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
        (z2PeriodicHypercubicOrientedExplicitDobrushinRate beta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) :=
      z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_explicitGreenTail_automaticL1_of_beta_lt
        n hn beta hBeta.le sourcePlaquette targetPlaquette hBetaLt
    _ =
      16 *
        (Real.exp
            (-z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta *
              (periodicHypercubicPlaquetteBaseL1DecayRadius
                n sourcePlaquette targetPlaquette : ℝ)) /
          (1 -
            z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) := by
      rw [z2PeriodicHypercubicOrientedExplicitDobrushinRate_pow_eq_exp_neg_decayRate_mul
        beta hBeta]

end

end MathlibAnalytic
end MGAP4D
