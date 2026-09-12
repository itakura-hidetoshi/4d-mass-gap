import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveDensityGaugeInvariance
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonBoundaryFiberedGibbsTransport

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundaryEffectiveMeasureGaugeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryEffectiveMeasureGaugeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryEffectiveMeasureGaugeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryEffectiveMeasureGaugeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryEffectiveMeasureGaugeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The effective finite Wilson boundary measure obtained by weighting boundary
Haar measure by the actual marginal density generated from the squared vacuum
moment. -/
noncomputable def periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) :=
  (periodicHypercubicEvenBoundaryHaarMeasure H N).withDensity
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
      H N hN beta hbeta)

/-- The actual effective finite Wilson boundary measure is gauge invariant.

The proof uses Mathlib measure transport rather than a new physical hypothesis:
`Measure.map` transports `withDensity` through the already constructed measurable
gauge equivalence, product Haar is measure-preserving, and the transported
density is pointwise fixed by the inverse gauge action. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_map_gauge_eq_self
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure.map (periodicHypercubicEvenBoundaryGaugeTransform H N gamma)
        (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        H N hN beta hbeta := by
  let e := periodicHypercubicEvenBoundaryGaugeMeasurableEquiv H N gamma
  unfold periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
  change
    Measure.map e
        ((periodicHypercubicEvenBoundaryHaarMeasure H N).withDensity
          (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
            H N hN beta hbeta)) =
      (periodicHypercubicEvenBoundaryHaarMeasure H N).withDensity
        (periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta)
  rw [MGAP4D.MathlibAnalytic.MeasurableEquiv.map_withDensity_comp_symm_transport
    e
    (periodicHypercubicEvenBoundaryHaarMeasure H N)
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity H N hN beta hbeta)
    (periodicHypercubicEvenBoundaryMarginalEffectiveDensity_measurable
      H N hN beta hbeta)]
  have hHaar :
      Measure.map e (periodicHypercubicEvenBoundaryHaarMeasure H N) =
        periodicHypercubicEvenBoundaryHaarMeasure H N := by
    change
      Measure.map (periodicHypercubicEvenBoundaryGaugeTransform H N gamma)
          (periodicHypercubicEvenBoundaryHaarMeasure H N) =
        periodicHypercubicEvenBoundaryHaarMeasure H N
    exact
      (periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving
        H N gamma).map_eq
  have hDensity :
      (fun b =>
        periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta (e.symm b)) =
        periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta := by
    funext b
    change
      periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta
          (periodicHypercubicEvenBoundaryGaugeTransform H N
            (fun v => (gamma v)⁻¹) b) =
        periodicHypercubicEvenBoundaryMarginalEffectiveDensity
          H N hN beta hbeta b
    exact periodicHypercubicEvenBoundaryMarginalEffectiveDensity_gaugeInvariant
      H N hN beta hbeta (fun v => (gamma v)⁻¹) b
  rw [hHaar, hDensity]

end

end MathlibAnalytic
end MGAP4D
