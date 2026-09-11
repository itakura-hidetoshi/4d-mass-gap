import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCofinalPlaquetteCovariance

namespace MGAP4D.MathlibAnalytic

noncomputable section

theorem PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData.approx_abs_le
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ} {hBeta : 0 < beta} {distance : ℕ}
    (K : Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate beta hBeta)
    (B : PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData S beta hBeta distance)
    (k : ℕ) :
    abs (S.approximatingConnectedCorrelation k B.sourceObservable B.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta * (distance : ℝ)) := by
  letI : NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k)) :=
    ⟨by unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume; omega⟩
  have h := K.covariance_abs_le
    (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (B.index k))
    (z2PeriodicHypercubicOrientedPlaquetteLimitVolume_ge_three (B.index k))
    (B.sourcePlaquette k) (B.targetPlaquette k)
  rw [B.distance_eq k, B.finiteCovariance_eq k] at h
  exact h

end

end MGAP4D.MathlibAnalytic
