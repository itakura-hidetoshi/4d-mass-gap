import MGAP4D.MathlibAnalytic.PhysicalYangMillsZ2PeriodicCanonicalScaling
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

local instance (index : ℕ → ℕ) (k : ℕ) :
    NeZero (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k)) :=
  ⟨by
    unfold z2PeriodicHypercubicOrientedPlaquetteLimitVolume
    omega⟩

/-- Plaquette data for a weak limit indexed by a strict cofinal subsequence of
canonical periodic volumes. -/
structure PhysicalYangMillsZ2PeriodicCofinalPlaquetteWeakLimitData
    (S : PhysicalFourDimensionalYangMillsWeakLimit)
    (beta : ℝ) (hBeta : 0 < beta) (distance : ℕ) where
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  interpolate :
    ∀ k : ℕ,
      (z2PeriodicHypercubicOrientedWilsonSystem
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
        beta hBeta.le).Configuration → S.Configuration
  interpolate_measurable : ∀ k : ℕ, Measurable (interpolate k)
  approximatingMeasure_eq_map :
    ∀ k : ℕ,
      (S.approximatingMeasure k : Measure S.Configuration) =
        Measure.map (interpolate k)
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
            beta hBeta.le).gibbsMeasure
  sourceObservable : BoundedContinuousFunction S.Configuration ℝ
  targetObservable : BoundedContinuousFunction S.Configuration ℝ
  sourcePlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
  targetPlaquette :
    ∀ k : ℕ,
      PeriodicHypercubicPlaquette
        (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
  distance_eq :
    ∀ k : ℕ,
      periodicHypercubicPlaquetteBaseL1Distance
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
          (sourcePlaquette k) (targetPlaquette k) = distance
  source_pullback :
    ∀ (k : ℕ)
      (U :
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
          beta hBeta.le).Configuration),
      sourceObservable (interpolate k U) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
            beta hBeta.le)
          (sourcePlaquette k) U
  target_pullback :
    ∀ (k : ℕ)
      (U :
        (z2PeriodicHypercubicOrientedWilsonSystem
          (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
          beta hBeta.le).Configuration),
      targetObservable (interpolate k U) =
        FiniteOrientedLatticeWilsonSystem.plaquetteObservable
          (z2PeriodicHypercubicOrientedWilsonSystem
            (z2PeriodicHypercubicOrientedPlaquetteLimitVolume (index k))
            beta hBeta.le)
          (targetPlaquette k) U

end

end MathlibAnalytic
end MGAP4D
