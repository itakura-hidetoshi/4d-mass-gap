import MGAP4D.MathlibAnalytic.Z2PeriodicCofinalContinuumClustering
import MGAP4D.MathlibAnalytic.PhysicalYangMillsProkhorovLimit

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (f : ℕ → ℕ) (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (f k)) :=
  ⟨by unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume; omega⟩

/-- Canonical plaquette data and a Prokhorov subsequence determine cofinal weak
limit data without a new covariance-identification assumption. -/
noncomputable def PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData.toProkhorovCofinalData
    {beta : ℝ} {hBeta : 0 < beta}
    {E : PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding beta hBeta}
    {distance : ℕ}
    (D : PhysicalYangMillsZ2PeriodicCanonicalPlaquetteData E distance)
    (L : PhysicalFourDimensionalYangMillsProkhorovSubsequenceLimit E.toLatticeEmbedding) :
    PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData
      L.toWeakLimit beta hBeta distance :=
  { index := L.subsequence
    index_strictMono := L.subsequence_strictMono
    interpolate := fun k U => E.interpolate (L.subsequence k) U
    interpolate_measurable := fun k => E.interpolate_measurable (L.subsequence k)
    approximatingMeasure_eq_map := fun k => by
      change ProbabilityMeasure.toMeasure
        (E.toLatticeEmbedding.embeddedMeasure (L.subsequence k)) = _
      simpa [PhysicalYangMillsZ2PeriodicCanonicalLatticeEmbedding.realize] using
        PhysicalYangMillsZ2PeriodicLatticeEmbeddingBridge.embeddedMeasure_toMeasure_eq_composite_map
          D.toLatticeEmbeddingBridge (L.subsequence k)
    sourceObservable := D.sourceObservable
    targetObservable := D.targetObservable
    sourcePlaquette := fun k => D.sourcePlaquette (L.subsequence k)
    targetPlaquette := fun k => D.targetPlaquette (L.subsequence k)
    distance_eq := fun k => D.distance_eq (L.subsequence k)
    source_pullback := fun k U => D.source_pullback (L.subsequence k) U
    target_pullback := fun k U => D.target_pullback (L.subsequence k) U }

end

end MGAP4D.MathlibAnalytic
