import MGAP4D.MathlibAnalytic.Z2PeriodicCofinalApproxBound

namespace MGAP4D.MathlibAnalytic

open Filter

noncomputable section

theorem PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData.continuum_abs_le
    {S : PhysicalFourDimensionalYangMillsWeakLimit}
    {beta : ℝ} {hBeta : 0 < beta} {distance : ℕ}
    (K : Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate beta hBeta)
    (B : PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData S beta hBeta distance) :
    abs (S.continuumConnectedCorrelation B.sourceObservable B.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta * (distance : ℝ)) := by
  have hlim :=
    (physical_yang_mills_bounded_observable_connectedCorrelation_converges
      S B.sourceObservable B.targetObservable).abs
  exact isClosed_Iic.mem_of_tendsto hlim
    (Filter.Eventually.of_forall (B.approx_abs_le K))

end

end MGAP4D.MathlibAnalytic
