import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCanonicalProkhorovBridge

namespace MGAP4D.MathlibAnalytic

noncomputable section

noncomputable def PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.prokhorovLimitOfTight
    {beta : ℝ} {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (_D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (hTight : E.toLatticeEmbedding.IsTight) :
    PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E.toLatticeEmbedding :=
  (physical_yang_mills_prokhorov_subsequence_exists E.toLatticeEmbedding hTight).some

/-- Tightness yields a subsequential continuum probability measure whose
selected connected plaquette correlation has the explicit exponential bound. -/
theorem PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.continuum_abs_le_of_tight
    {beta : ℝ} {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (K : Z2PeriodicHypercubicOrientedPlaquetteUniformSpatialClusteringFamilyCertificate beta hBeta)
    (hTight : E.toLatticeEmbedding.IsTight) :
    let L := D.prokhorovLimitOfTight hTight
    abs (L.toWeakLimit.continuumConnectedCorrelation
      D.sourceObservable D.targetObservable) ≤
      z2PeriodicHypercubicOrientedExplicitSpatialClusteringPrefactor beta *
        Real.exp (-z2PeriodicHypercubicOrientedExplicitSpatialClusteringRate beta * (distance : ℝ)) := by
  dsimp only
  exact (D.toProkhorovCofinalData (D.prokhorovLimitOfTight hTight)).continuum_abs_le K

end

end MGAP4D.MathlibAnalytic
