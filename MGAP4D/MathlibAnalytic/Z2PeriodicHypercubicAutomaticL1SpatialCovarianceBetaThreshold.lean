import MGAP4D.MathlibAnalytic.PeriodicHypercubicAutomaticL1SpatialCovarianceNonempty
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedExplicitDobrushin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit small-coupling threshold obtained from the periodic oriented
`Z₂` active-neighbor bound `18` and the one-plaquette influence majorant. -/
def z2PeriodicHypercubicOrientedDobrushinBetaThreshold : ℝ :=
  Real.log ((19 : ℝ) / 17) / 2

/-- The internally normalized canonical coefficient obeys the existing
`18 × eta` explicit coupling estimate. -/
theorem z2PeriodicHypercubicCanonicalDobrushinCoefficient_le_eighteen_mul_eta
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta ≤
      18 * z2PeriodicHypercubicOrientedDobrushinEta beta := by
  simpa [z2PeriodicHypercubicCanonicalDobrushinCoefficient] using
    z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_le
      n hn beta hBeta

/-- The exponential threshold proves strictness of the internally normalized
canonical coefficient. -/
theorem z2PeriodicHypercubicCanonicalDobrushinCoefficient_lt_one_of_exp_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hExp : Real.exp (beta * 2) < (19 : ℝ) / 17) :
    z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta < 1 := by
  exact lt_of_le_of_lt
    (z2PeriodicHypercubicCanonicalDobrushinCoefficient_le_eighteen_mul_eta
      n hn beta hBeta)
    (z2PeriodicHypercubicOriented_eighteen_mul_eta_lt_one_of_exp_lt
      beta hExp)

/-- The explicit logarithmic small-coupling condition proves strictness of the
internally normalized canonical coefficient. -/
theorem z2PeriodicHypercubicCanonicalDobrushinCoefficient_lt_one_of_beta_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta < 1 := by
  simpa [z2PeriodicHypercubicCanonicalDobrushinCoefficient,
    z2PeriodicHypercubicOrientedDobrushinBetaThreshold] using
      z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_lt_one_of_beta_lt
        n hn beta hBeta hBetaLt

/-- Automatic finite-volume periodic `Z₂` plaquette covariance decay under the
explicit exponential coupling threshold.  The spatial exponent and physical
edge nonemptiness remain internal. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1_of_exp_lt
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
        (z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicCanonicalDobrushinCoefficient
              n beta hBeta)) := by
  exact
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1_of_canonicalStrict
      n beta hBeta sourcePlaquette targetPlaquette
      (z2PeriodicHypercubicCanonicalDobrushinCoefficient_lt_one_of_exp_lt
        n hn beta hBeta hExp)

/-- Automatic finite-volume periodic `Z₂` plaquette covariance decay under the
explicit logarithmic small-coupling condition
`beta < log (19 / 17) / 2`. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1_of_beta_lt
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
        (z2PeriodicHypercubicCanonicalDobrushinCoefficient n beta hBeta ^
            periodicHypercubicPlaquetteBaseL1DecayRadius
              n sourcePlaquette targetPlaquette /
          (1 -
            z2PeriodicHypercubicCanonicalDobrushinCoefficient
              n beta hBeta)) := by
  exact
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_sixteen_mul_canonicalGreenTail_automaticL1_of_canonicalStrict
      n beta hBeta sourcePlaquette targetPlaquette
      (z2PeriodicHypercubicCanonicalDobrushinCoefficient_lt_one_of_beta_lt
        n hn beta hBeta hBetaLt)

end

end MathlibAnalytic
end MGAP4D
