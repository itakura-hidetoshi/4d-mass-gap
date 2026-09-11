import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteSpatialClusteringCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A volume-uniform family certificate for finite periodic oriented `Z₂`
plaquette spatial clustering.

The beta-only clustering rate and prefactor are shared by every finite lattice
size `n ≥ 3`.  The certificate does not assert an infinite-volume Gibbs state,
convergence in the volume parameter, a transfer-matrix gap, or a physical mass. -/
structure
    Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
    (beta : ℝ)
    (hBeta : 0 < beta) where
  highTemperature :
    beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold
  clusteringRate_pos :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta
  clusteringPrefactor_pos :
    0 < z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta
  finiteVolumeCertificate :
    ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n),
      Z2PeriodicHypercubicOrientedPlaquetteSpatialClusteringCertificate
        n beta hBeta

/-- Assemble the volume-uniform family certificate from the explicit
high-temperature condition. -/
noncomputable def
    z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
    (beta : ℝ)
    (hBeta : 0 < beta)
    (hBetaLt :
      beta < z2PeriodicHypercubicOrientedDobrushinBetaThreshold) :
    Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
      beta hBeta :=
  { highTemperature := hBetaLt
    clusteringRate_pos :=
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate_pos
        beta hBeta hBetaLt
    clusteringPrefactor_pos :=
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor_pos
        beta hBetaLt
    finiteVolumeCertificate := fun n _ hn =>
      z2PeriodicHypercubicOrientedPlaquetteSpatialClusteringCertificate
        n hn beta hBeta hBetaLt }

/-- Extract the finite-volume spatial-clustering certificate at any lattice
size `n ≥ 3` from the uniform family certificate. -/
theorem
    Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate.finiteVolume
    {beta : ℝ}
    {hBeta : 0 < beta}
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n) :
    Z2PeriodicHypercubicOrientedPlaquetteSpatialClusteringCertificate
      n beta hBeta :=
  K.finiteVolumeCertificate n hn

/-- The beta-only constants of a uniform family certificate control every pair
of plaquettes in every finite periodic volume `n ≥ 3`. -/
theorem
    Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate.covariance_abs_le
    {beta : ℝ}
    {hBeta : 0 < beta}
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (sourcePlaquette targetPlaquette : PeriodicHypercubicPlaquette n) :
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
              n sourcePlaquette targetPlaquette : ℝ)) :=
  (K.finiteVolume n hn).covariance_abs_le
    sourcePlaquette targetPlaquette

end

end MathlibAnalytic
end MGAP4D
