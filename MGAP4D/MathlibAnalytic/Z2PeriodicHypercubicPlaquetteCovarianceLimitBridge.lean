import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicPlaquetteUniformSpatialClusteringFamilyCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A canonical cofinal sequence of finite periodic side lengths beginning at
three. -/
def z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    (k : ℕ) : ℕ :=
  k + 3

local instance (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- Every volume in the canonical sequence has side length at least three. -/
theorem z2PeriodicHypercubicOrientedPlaquetteLimitVolume_ge_three
    (k : ℕ) :
    3 ≤ z2PeriodicHypercubicOrientedPlaquetteLimitVolume k := by
  unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
  omega

/-- Model-dependent data identifying a fixed pair of local plaquette
observables across a cofinal sequence of finite periodic volumes and asserting
convergence of their finite-volume covariances to one limiting scalar.

The bridge does not construct the limit, an infinite-volume Gibbs measure, or
an embedding of the finite configuration spaces.  Those data must be supplied
independently. -/
structure
    Z2PeriodicHypercubicOrientedPlaquetteCovarianceLimitBridge
    (beta : ℝ)
    (hBeta : 0 < beta)
    (distance : ℕ) where
  sourcePlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  targetPlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
  distance_eq :
    ∀ k : ℕ,
      periodicHypercubicPlaquetteBaseL1Distance
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
          (sourcePlaquette k)
          (targetPlaquette k) =
        distance
  limitingCovariance : ℝ
  covariance_tendsto :
    Tendsto
      (fun k : ℕ =>
        FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
            beta hBeta.le)
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem
              (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
              beta hBeta.le)
            (sourcePlaquette k))
          (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
            (z2PeriodicHypercubicOrientedWilsonSystem
              (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
              beta hBeta.le)
            (targetPlaquette k)))
      atTop
      (nhds limitingCovariance)

/-- A volume-uniform finite-volume clustering estimate passes to any supplied
scalar covariance limit for a fixed-distance family of plaquette observables. -/
theorem
    Z2PeriodicHypercubicOrientedPlaquetteCovarianceLimitBridge.limitingCovariance_abs_le
    {beta : ℝ}
    {hBeta : 0 < beta}
    {distance : ℕ}
    (K :
      Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate
        beta hBeta)
    (B :
      Z2PeriodicHypercubicOrientedPlaquetteCovarianceLimitBridge
        beta hBeta distance) :
    |B.limitingCovariance| ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp
          (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
            (distance : ℝ)) := by
  have hFinite :
      ∀ k : ℕ,
        |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
            (z2PeriodicHypercubicOrientedWilsonSystem
              (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
              beta hBeta.le)
            (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
              (z2PeriodicHypercubicOrientedWilsonSystem
                (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
                beta hBeta.le)
              (B.sourcePlaquette k))
            (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
              (z2PeriodicHypercubicOrientedWilsonSystem
                (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
                beta hBeta.le)
              (B.targetPlaquette k))| ≤
          z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
            Real.exp
              (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta *
                (distance : ℝ)) := by
    intro k
    have hBound :=
      K.covariance_abs_le
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume_ge_three k)
        (B.sourcePlaquette k)
        (B.targetPlaquette k)
    rw [B.distance_eq k] at hBound
    exact hBound
  have hAbsTendsto :
      Tendsto
        (fun k : ℕ =>
          |FiniteOrientedLatticeWilsonSystem.gibbsCovarianceReal
              (z2PeriodicHypercubicOrientedWilsonSystem
                (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
                beta hBeta.le)
              (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
                (z2PeriodicHypercubicOrientedWilsonSystem
                  (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
                  beta hBeta.le)
                (B.sourcePlaquette k))
              (FiniteOrientedLatticeWilsonSystem.plaquetteObservable
                (z2PeriodicHypercubicOrientedWilsonSystem
                  (z2PeriodicHypercubicOrientedPlaquetteLimitVolume k)
                  beta hBeta.le)
                (B.targetPlaquette k))|)
        atTop
        (nhds |B.limitingCovariance|) :=
    B.covariance_tendsto.abs
  exact isClosed_Iic.mem_of_tendsto hAbsTendsto
    (Filter.Eventually.of_forall hFinite)

end

end MathlibAnalytic
end MGAP4D
