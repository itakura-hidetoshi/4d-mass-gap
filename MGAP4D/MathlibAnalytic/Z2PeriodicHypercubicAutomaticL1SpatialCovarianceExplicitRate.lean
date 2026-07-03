import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicAutomaticL1SpatialCovarianceBetaThreshold
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit periodic oriented `Z₂` Dobrushin rate obtained from the
active-neighbor bound `18` and the one-plaquette influence majorant. -/
def z2PeriodicHypercubicOrientedExplicitDobrushinRate
    (beta : ℝ) : ℝ :=
  18 *
    ((Real.exp (beta * 2) - 1) /
      (Real.exp (beta * 2) + 1))

/-- The explicit rate is the existing `18 × eta` majorant. -/
theorem z2PeriodicHypercubicOrientedExplicitDobrushinRate_eq
    (beta : ℝ) :
    z2PeriodicHypercubicOrientedExplicitDobrushinRate beta =
      18 * z2PeriodicHypercubicOrientedDobrushinEta beta := by
  rfl

/-- The explicit rate is nonnegative for nonnegative coupling. -/
theorem z2PeriodicHypercubicOrientedExplicitDobrushinRate_nonneg
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    0 ≤ z2PeriodicHypercubicOrientedExplicitDobrushinRate beta := by
  have hExpOne : 1 ≤ Real.exp (beta * 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  unfold z2PeriodicHypercubicOrientedExplicitDobrushinRate
  exact mul_nonneg (by norm_num)
    (div_nonneg (sub_nonneg.mpr hExpOne) (by positivity))

/-- The internally normalized canonical coefficient is nonnegative. -/
theorem z2PeriodicHypercubicCanonicalDobrushinCoefficient_nonneg
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    0 ≤ z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta := by
  simpa [z2PeriodicHypercubicCanonicalDobrushinCoefficient] using
    finite_oriented_canonicalDobrushinCoefficient_nonneg
      (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
      (periodicHypercubicEdge_card_pos n)

/-- The canonical coefficient is bounded by the explicit beta-only rate. -/
theorem z2PeriodicHypercubicCanonicalDobrushinCoefficient_le_explicitRate
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta ≤
      z2PeriodicHypercubicOrientedExplicitDobrushinRate beta := by
  simpa [z2PeriodicHypercubicOrientedExplicitDobrushinRate_eq] using
    z2PeriodicHypercubicCanonicalDobrushinCoefficient_le_eighteen_mul_eta
      n hn beta hBeta

/-- The exponential threshold makes the explicit beta-only rate strict. -/
theorem z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_exp_lt
    (beta : ℝ)
    (hExp : Real.exp (beta * 2) < (19 : ℝ) / 17) :
    z2PeriodicHypercubicOrientedExplicitDobrushinRate beta < 1 := by
  simpa [z2PeriodicHypercubicOrientedExplicitDobrushinRate_eq] using
    z2PeriodicHypercubicOriented_eighteen_mul_eta_lt_one_of_exp_lt
      beta hExp

/-- The logarithmic small-coupling condition implies the exponential
threshold used by the explicit rate. -/
theorem z2PeriodicHypercubicOriented_exp_two_mul_lt_ratio_of_beta_lt
    (beta : ℝ)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    Real.exp (beta * 2) < (19 : ℝ) / 17 := by
  have hBetaLt' := hBetaLt
  rw [z2PeriodicHypercubicOrientedDobrushinBetaThreshold] at hBetaLt'
  have hArg : beta * 2 < Real.log ((19 : ℝ) / 17) := by
    nlinarith
  have hRatioPos : 0 < (19 : ℝ) / 17 := by
    norm_num
  calc
    Real.exp (beta * 2) <
        Real.exp (Real.log ((19 : ℝ) / 17)) :=
      Real.exp_lt_exp.mpr hArg
    _ = (19 : ℝ) / 17 := Real.exp_log hRatioPos

/-- The logarithmic small-coupling condition makes the explicit beta-only
rate strict. -/
theorem z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_beta_lt
    (beta : ℝ)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    z2PeriodicHypercubicOrientedExplicitDobrushinRate beta < 1 :=
  z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_exp_lt
    beta
    (z2PeriodicHypercubicOriented_exp_two_mul_lt_ratio_of_beta_lt
      beta hBetaLt)

/-- A geometric Green tail is monotone in its rate on the strict unit interval. -/
theorem finite_oriented_geometricGreenTail_mono
    {c q : ℝ}
    (hc : 0 ≤ c)
    (hcq : c ≤ q)
    (hq : q < 1)
    (d : ℕ) :
    c ^ d / (1 - c) ≤ q ^ d / (1 - q) := by
  have hcLt : c < 1 := lt_of_le_of_lt hcq hq
  have hcDen : 0 < 1 - c := sub_pos.mpr hcLt
  have hqDen : 0 < 1 - q := sub_pos.mpr hq
  have hqNonneg : 0 ≤ q := le_trans hc hcq
  have hPow : c ^ d ≤ q ^ d :=
    pow_le_pow_left₀ hc hcq d
  apply (div_le_div_iff₀ hcDen hqDen).2
  calc
    c ^ d * (1 - q) ≤ q ^ d * (1 - q) :=
      mul_le_mul_of_nonneg_right hPow hqDen.le
    _ ≤ q ^ d * (1 - c) := by
      apply mul_le_mul_of_nonneg_left
      · linarith
      · exact pow_nonneg hqNonneg d

/-- Automatic finite-volume periodic `Z₂` plaquette covariance decay with the
canonical coefficient replaced by the explicit beta-only rate, under the
exponential threshold. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_explicitGreenTail_automaticL1_of_exp_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hExp : Real.exp (beta * 2) < (19 : ℝ) / 17) :
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      16 *
        (z2PeriodicHypercubicOrientedExplicitDobrushinRate beta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) := by
  calc
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      16 *
        (z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicCanonicalDobrushinCoefficient
              n beta hBeta)) :=
      z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1_of_exp_lt
        n hn beta hBeta sourcePlaquette targetPlaquette hExp
    _ ≤
      16 *
        (z2PeriodicHypercubicOrientedExplicitDobrushinRate beta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) := by
      apply mul_le_mul_of_nonneg_left
      · exact finite_oriented_geometricGreenTail_mono
          (z2PeriodicHypercubicCanonicalDobrushinCoefficient_nonneg
            n beta hBeta)
          (z2PeriodicHypercubicCanonicalDobrushinCoefficient_le_explicitRate
            n hn beta hBeta)
          (z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_exp_lt
            beta hExp)
          (periodicHypercubicPlaquetteBaseL1DecayRadius
            n sourcePlaquette targetPlaquette)
      · norm_num

/-- Automatic finite-volume periodic `Z₂` plaquette covariance decay with a
right-hand side depending only on beta and the automatic periodic `L¹` decay
radius, under `beta < log (19 / 17) / 2`. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_explicitGreenTail_automaticL1_of_beta_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ) (hBeta : 0 ≤ beta)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
        (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          sourcePlaquette)
        (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta)
          targetPlaquette)| ≤
      16 *
        (z2PeriodicHypercubicOrientedExplicitDobrushinRate beta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)) := by
  exact
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_explicitGreenTail_automaticL1_of_exp_lt
      n hn beta hBeta sourcePlaquette targetPlaquette
      (z2PeriodicHypercubicOriented_exp_two_mul_lt_ratio_of_beta_lt
        beta hBetaLt)

end

end MathlibAnalytic
end MGAP4D
