import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfHaarTemporalGaugeReduction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

/-- After exact temporal-link Haar gauge fixing, the positive-half Gauss-endpoint
amplitude is literally the finite Markov-chain integral of the `H+1` adjacent
temporal-gauge one-slab Wilson kernels.  No abstract transfer operator, spectral
input, or continuum hypothesis occurs in this identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_iteratedHaar_integral_eq_oneSlabChain
    (H N : ℕ)
    (beta : ℝ)
    (f g : Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))
    (hg : g ∈ periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ U,
      (∫ path,
        f (path 0) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderUnfixedPathKernel
            H N beta path U *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N))
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalFieldHaarMeasure H N)) =
      ∫ path,
        f (path 0) *
          (∏ i : Fin (periodicHypercubicEvenPositiveHalfCylinderSlabCount H),
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              H N beta (path i.castSucc) (path i.succ)) *
          g (path (Fin.last (periodicHypercubicEvenPositiveHalfCylinderSlabCount H)))
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPositiveHalfGaussEndpoint_iteratedHaar_integral_eq_temporalGauge
    H N beta f g hg]
  rfl

end

end MathlibAnalytic
end MGAP4D
