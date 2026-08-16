import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryMarginalEffectiveMeasureGaugeInvariance
import Mathlib.Topology.ContinuousMap.Bounded.Normed

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance boundaryEffectiveObservableGaugeTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance boundaryEffectiveObservableGaugeCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance boundaryEffectiveObservableGaugeSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance boundaryEffectiveObservableGaugeMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance boundaryEffectiveObservableGaugeBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Every actual finite boundary gauge transformation preserves the effective
Wilson boundary measure generated from the squared vacuum moment. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_measurePreserving
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MeasurePreserving
      (periodicHypercubicEvenBoundaryGaugeTransform H N gamma)
      (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        H N hN beta hbeta)
      (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        H N hN beta hbeta) :=
  ⟨(periodicHypercubicEvenBoundaryGaugeTransform_measurePreserving
      H N gamma).measurable,
    periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_map_gauge_eq_self
      H N hN beta hbeta gamma⟩

/-- Expectations of bounded continuous observables on the actual effective
Wilson boundary law are unchanged by every finite boundary gauge
transformation.

This is the finite-volume observable-level form of gauge invariance needed by
later interpolation and physical-state bridges.  It follows only from
`MeasureTheory.integral_map` and the generated effective-measure invariance. -/
theorem periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_boundedObservable_expectation_gaugeInvariant
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (gamma : PeriodicHypercubicEvenVertex H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitaryBoundaryConfiguration H N) ℝ) :
    (∫ b, O (periodicHypercubicEvenBoundaryGaugeTransform H N gamma b)
      ∂periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
        H N hN beta hbeta) =
      ∫ b, O b
        ∂periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
          H N hN beta hbeta := by
  let μ := periodicHypercubicEvenBoundaryMarginalEffectiveMeasure
    H N hN beta hbeta
  let T := periodicHypercubicEvenBoundaryGaugeTransform H N gamma
  have hT : Measurable T :=
    (periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_measurePreserving
      H N hN beta hbeta gamma).measurable
  calc
    (∫ b, O (T b) ∂μ) =
        ∫ b, O b ∂Measure.map T μ := by
      symm
      exact MeasureTheory.integral_map
        hT.aemeasurable O.continuous.aestronglyMeasurable
    _ = ∫ b, O b ∂μ := by
      rw [periodicHypercubicEvenBoundaryMarginalEffectiveMeasure_map_gauge_eq_self
        H N hN beta hbeta gamma]

end

end MathlibAnalytic
end MGAP4D
