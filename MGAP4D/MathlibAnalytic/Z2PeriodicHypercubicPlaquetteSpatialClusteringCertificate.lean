import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteBaseL1SpatialCovarianceExplicitExponentialDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit finite-volume spatial-clustering rate per unit of raw periodic
plaquette-base `L¹` distance.  It is one half of the automatic-radius decay
rate and is not a transfer-matrix spectral gap or a physical mass. -/
def z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate
    (beta : ℝ) : ℝ :=
  z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2

/-- The beta-dependent prefactor in the raw-distance finite-volume spatial
clustering estimate.  It is independent of the lattice size and plaquettes. -/
def z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor
    (beta : ℝ) : ℝ :=
  16 *
      Real.exp
        (3 * z2PeriodicHypercubicOrientedExplicitSpatialDecayRate beta / 2) /
    (1 - z2PeriodicHypercubicOrientedExplicitDobrushinRate beta)

/-- The explicit raw-distance clustering rate is positive in the stated
high-temperature interval. -/
theorem z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate_pos
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta := by
  unfold z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate
  exact div_pos
    (z2PeriodicHypercubicOrientedExplicitSpatialDecayRate_pos
      beta hBeta hBetaLt)
    (by norm_num)

/-- The explicit raw-distance clustering prefactor is strictly positive in the
stated high-temperature interval. -/
theorem z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor_pos
    (beta : ℝ)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta := by
  unfold z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor
  exact div_pos
    (mul_pos (by norm_num) (Real.exp_pos _))
    (sub_pos.mpr
      (z2PeriodicHypercubicOrientedExplicitDobrushinRate_lt_one_of_beta_lt
        beta hBetaLt))

/-- The raw-distance covariance estimate written through named beta-only
clustering constants. -/
theorem
    z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_explicitSpatialClustering_of_beta_lt
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
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (periodicHypercubicPlaquetteBaseL1Distance
              n sourcePlaquette targetPlaquette : ℝ)) := by
  simpa
    [z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate,
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor] using
    (z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_exp_neg_half_explicitDecayRate_mul_plaquetteBaseL1Distance_of_beta_lt
      n hn beta hBeta sourcePlaquette targetPlaquette hBetaLt)

/-- A finite-volume certificate for periodic oriented `Z₂` plaquette spatial
clustering.  The named rate and prefactor depend only on beta; the certificate
records the lattice-size and high-temperature hypotheses together with the
covariance estimate for every pair of plaquettes in the selected volume. -/
structure Z2PeriodicHypercubicOrientedPlaquetteSpatialClusteringCertificate
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (hBeta : 0 < beta) where
  latticeSize : 3 ≤ n
  highTemperature :
    beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold
  clusteringRate_pos :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta
  clusteringPrefactor_pos :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta
  covariance_abs_le :
    ∀ sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n,
      |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
          (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
            sourcePlaquette)
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta.le)
            targetPlaquette)| ≤
        z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
          Real.exp
            (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
              (periodicHypercubicPlaquetteBaseL1Distance
                n sourcePlaquette targetPlaquette : ℝ))

/-- Assemble the finite-volume spatial-clustering certificate from the explicit
high-temperature condition. -/
noncomputable def
    z2PeriodicHypercubicOrientedPlaquetteSpatialClusteringCertificate
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    Z2PeriodicHypercubicOrientedPlaquetteSpatialClusteringCertificate
      n beta hBeta :=
  { latticeSize := hn
    highTemperature := hBetaLt
    clusteringRate_pos :=
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate_pos
        beta hBeta hBetaLt
    clusteringPrefactor_pos :=
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor_pos
        beta hBetaLt
    covariance_abs_le := fun sourcePlaquette targetPlaquette =>
      z2PeriodicHypercubicOrientedPlaquetteGibbsCovariance_abs_le_explicitSpatialClustering_of_beta_lt
        n hn beta hBeta sourcePlaquette targetPlaquette hBetaLt }

end

end MathlibAnalytic
end MGAP4D
