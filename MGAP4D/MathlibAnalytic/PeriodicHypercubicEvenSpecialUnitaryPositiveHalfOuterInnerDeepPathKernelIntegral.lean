import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepCoordinateReceipts
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfOuterInnerDeepPathKernelIntegralIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfOuterInnerDeepPathKernelIntegralCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfOuterInnerDeepPathKernelIntegralSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfOuterInnerDeepPathKernelIntegralMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfOuterInnerDeepPathKernelIntegralBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfOuterInnerDeepPathKernelIntegralSpatialLinkFintype (M : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink (M + 2)) :=
  Fintype.ofFinite _

/-- The explicit carrier of the three-factor nondegenerate Haar coordinates:
outer endpoint pair, inward endpoint pair, then the deeper interior path. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialCoordinates
    (M N : ℕ) : Type :=
  (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
    ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (M + 2) N) ×
      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfDeepInteriorSpatialPath M N)

/-- The untouched interior Wilson product, regarded as a function of the
three-factor Haar coordinates by reconstructing the unique complete spatial
path through the canonical measurable equivalence. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
    (M N : ℕ)
    (beta : ℝ)
    (q : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialCoordinates M N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugeInteriorPathKernel
    (M + 2) N beta
    ((periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
      M N).symm q)

/-- Markov form of the complete positive-half path kernel in the three-factor
coordinates.  The ambient pair-Haar one-step kernel sees only the exposed outer
and inner pairs; every remaining slab factor is retained in the reconstructed
interior kernel. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
    (M N : ℕ)
    (beta : ℝ)
    (q : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialCoordinates M N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
      (M + 2) N beta (q.1, q.2.1) *
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel
      M N beta q

/-- Pulling the three-factor Markov integrand back to an actual complete path
recovers the literal temporal-gauge path kernel pointwise.  This is where the
coordinate receipts identify the two exposed pair variables with the actual
outer and inward boundary pairs of the path factorization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_comp
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (path : PeriodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderSpatialPath (M + 2) N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
        M N beta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv
          M N path) =
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path := by
  have hFactor :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel_eq_pairKernel_mul_interior
      (M + 2) N (by omega) hN beta hbeta path
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepInteriorPathKernel] using
    hFactor.symm

/-- Exact Haar change of variables from the complete nondegenerate spatial path
to the exposed `outerPair × (innerPair × deep)` Markov coordinates.

No Fubini interchange is used yet: this theorem only transports the literal
path-kernel integral through the already-proved measure-preserving equivalence,
while the pointwise Markov factorization supplies the new integrand. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfTemporalGaugePathKernel_integral_eq_outerInnerDeep
    (M N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
      ∫ q,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
          M N beta q
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv M N
  let F :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand M N beta
  calc
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathKernel
        (M + 2) N beta path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N)) =
        ∫ path, F (e path)
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathHaarMeasure (M + 2) N) := by
      apply integral_congr_ae
      filter_upwards with path
      exact
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand_comp
          M N hN beta hbeta path).symm
    _ = ∫ q, F q
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfSpatialPathOuterInnerDeepMeasurableEquiv_measurePreserving
          M N).integral_comp' F
    _ = ∫ q,
        periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepMarkovIntegrand
          M N beta q
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfOuterInnerDeepSpatialHaarMeasure M N) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
