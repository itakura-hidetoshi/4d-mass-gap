import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenOSPositiveHalfClosureHaarPathTransport

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Bare positive-half specialization of the closure-to-path Haar transport.
With no bulk insertion, the genuine unnormalized OS positive-half amplitude
integrates exactly to the unfixed `H+1`-slab path kernel against the nested
spatial-path / temporal-field Haar law.  This statement is still before
any temporal-gauge reduction. -/
theorem periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_bareClosureIntegral_eq_nestedPathIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ z,
      periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
        H N hN beta hbeta z.1 z.2
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N)) =
      ∫ q,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
          H N beta q.1 q.2
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N) := by
  have h :=
    periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_closureIntegral_eq_nestedPathIntegral
      H N hN beta hbeta (fun _ => (1 : ℝ))
  simpa using h

/-- The same bare bridge in the reverse direction, convenient when a later
temporal-gauge or transfer-power theorem starts from the path-integral side. -/
theorem periodicHypercubicEvenSpecialUnitaryPositiveHalfBareNestedPathIntegral_eq_OSAmplitude_closureIntegral
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫ q,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
        H N beta q.1 q.2
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfNestedCoordinateHaarMeasure H N)) =
      ∫ z,
        periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude
          H N hN beta hbeta z.1 z.2
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfClosureHaarMeasure H N) :=
  (periodicHypercubicEvenBoundaryUnnormalizedPositiveHalfOSAmplitude_bareClosureIntegral_eq_nestedPathIntegral
    H N hN beta hbeta).symm

end

end MathlibAnalytic
end MGAP4D
