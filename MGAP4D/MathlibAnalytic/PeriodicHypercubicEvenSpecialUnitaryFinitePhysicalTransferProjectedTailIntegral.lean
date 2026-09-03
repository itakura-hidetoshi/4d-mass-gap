import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferProjectedTail
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferProjectedTailIntegralTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferProjectedTailIntegralCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferProjectedTailIntegralSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferProjectedTailIntegralMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferProjectedTailIntegralBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferProjectedTailIntegralSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The actual physical one-step coefficient against the Gauss-law projection
of the fixed-right Wilson kernel section. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta f)
    (periodicHypercubicEvenSpecialUnitaryGaussLawProjectedPhysicalVector H N
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelRightL2
        H N hN beta hbeta B))

/-- Literal two-consecutive-slab Wilson coefficient with the first boundary
weighted by the physical Haar-`L²` vector `f`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
    (H N : ℕ)
    (beta : ℝ)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.1 p.2 *
      ((f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) p.1 *
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H N beta p.2 B)
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)

/-- The packaged physical coefficient is exactly the literal two-slab raw Haar
coefficient. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient_eq_rawTwoSlab
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
        H N hN beta hbeta f B =
      periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient H N beta f B := by
  unfold periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
  unfold periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_projectedKernelRight_eq_rawTwoSlab
      H N hN beta hbeta f B

/-- The two-slab physical replacement is stable under integration over an
arbitrary later temporal path and multiplication by an arbitrary remainder
scalar.  This is the integrated projected-tail Markov step needed before
specializing `B` to the next actual spatial slice. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient_integral_laterTail
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (B : (Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (R : (Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    (∫ laterTail : Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
            H N hN beta hbeta f (B laterTail) * R laterTail
      ∂(Measure.pi (fun _ : Fin H =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N))) =
      ∫ laterTail : Fin H → PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
        periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
            H N beta f (B laterTail) * R laterTail
      ∂(Measure.pi (fun _ : Fin H =>
        periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
  apply integral_congr_ae
  filter_upwards with laterTail
  rw [periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient_eq_rawTwoSlab]

end

end MathlibAnalytic
end MGAP4D
