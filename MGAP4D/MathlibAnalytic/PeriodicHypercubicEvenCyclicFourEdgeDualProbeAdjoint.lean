import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCyclicFourEdgeTemporalCompanionTaylor

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

/-- The existing cyclic degree-`n` open-half scalar probe is exactly the
pairing against the Hilbert-adjoint pullback of its cyclic dual vector into the
genuine four-edge degree-`n` carrier.

The boundary and open-half cyclic feature constructions already use literally
the same completed Hilbert carrier.  Thus this theorem introduces no new
transport assumption: it only combines that canonical carrier identification
with the arbitrary-degree adjoint identity proved for the four-edge map. -/
theorem
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_eq_fourEdgePowerDualPullbackInner
    (H n : ℕ)
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q x =
      inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
          H n).feature x) := by
  rw [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_apply]
  symm
  simpa [periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbeVector,
    periodicHypercubicEvenPrimarySpatialPlaquetteBoundaryOpenHalfDegreeFeatureHilbertEquiv] using
    (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_temporalCompanionOpenHalf_feature
      H n q x)

/-- The preceding identity with the equality oriented from the adjoint source
pairing to the scalar cyclic probe, convenient for rewriting the inner
open-half Haar integrand exposed by the Wilson-analysis Fubini theorem. -/
theorem
    specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback_inner_temporalCompanionOpenHalf_feature_eq_probe
    (H n : ℕ)
    (q : (specialUnitaryTwoNormalizedTraceHilbertKernelFeature.pow n).FeatureHilbert)
    (x : (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
      (Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    inner ℝ
        (specialUnitaryTwoCyclicFourEdgeNormalizedTracePowerDualPullback n q)
        ((periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfFourEdgeDegreeFeature
          H n).feature x) =
      periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe
        H n q x := by
  exact
    (periodicHypercubicEvenPrimarySpatialPlaquetteTemporalCompanionOpenHalfDegreeDualProbe_eq_fourEdgePowerDualPullbackInner
      H n q x).symm

end

end MathlibAnalytic
end MGAP4D
