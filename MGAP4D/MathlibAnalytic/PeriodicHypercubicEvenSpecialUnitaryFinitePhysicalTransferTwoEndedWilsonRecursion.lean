import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryFinitePhysicalTransferWilsonRecursion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory
open scoped InnerProductSpace InnerProduct

local instance finitePhysicalTransferTwoEndedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance finitePhysicalTransferTwoEndedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance finitePhysicalTransferTwoEndedSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance finitePhysicalTransferTwoEndedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance finitePhysicalTransferTwoEndedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance finitePhysicalTransferTwoEndedSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The genuine remaining finite Wilson tail, including the physical terminal
boundary amplitude.  For `H = h+1`, `laterTail` contains `A₂,…,A_{h+2}`. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryWilsonLaterTailEndpointRemainder
    (h N : ℕ) (beta : ℝ)
    (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N)
    (laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryWilsonLaterTailRemainder h N beta laterTail *
    ((g : Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))
      (laterTail (Fin.last h)))

/-- The two-ended amplitude after replacing the first two raw Wilson slabs by
the actual physical one-step coefficient against the projected `A₂` section. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) : ℝ :=
  ∫ laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
    periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient
        (h + 1) N hN beta hbeta f (laterTail 0) *
      periodicHypercubicEvenSpecialUnitaryWilsonLaterTailEndpointRemainder
        h N beta g laterTail
  ∂(Measure.pi (fun _ : Fin (h + 1) =>
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))

/-- The same two-ended amplitude before the first two Wilson slabs are replaced
by a physical transfer coefficient. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryRawTwoEndedWilsonAmplitude
    (h N : ℕ) (beta : ℝ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) : ℝ :=
  ∫ laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
    periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
        (h + 1) N beta f (laterTail 0) *
      periodicHypercubicEvenSpecialUnitaryWilsonLaterTailEndpointRemainder
        h N beta g laterTail
  ∂(Measure.pi (fun _ : Fin (h + 1) =>
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))

/-- Literal finite Haar amplitude containing both physical endpoint vectors and
every adjacent one-slab Wilson kernel. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
    (h N : ℕ) (beta : ℝ)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) : ℝ :=
  ∫ laterTail : Fin (h + 1) →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
    ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N,
      ((f : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N)) p.1) *
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
            (h + 1) N beta p.1 p.2 *
          ∏ x : Fin (h + 1),
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
              (h + 1) N beta
              ((Fin.cons p.2 laterTail : Fin ((h + 1) + 1) →
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration (h + 1) N)
                x.castSucc)
              (laterTail x)) *
        ((g : Lp ℝ 2
          (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))
          (laterTail (Fin.last h)))
      ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure (h + 1) N)
  ∂(Measure.pi (fun _ : Fin (h + 1) =>
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure (h + 1) N))

/-- Projecting the actual next-boundary kernel section into the Gauss-law sector
does not change the complete two-ended finite Wilson amplitude. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_raw
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g =
      periodicHypercubicEvenSpecialUnitaryRawTwoEndedWilsonAmplitude h N beta f g := by
  unfold periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
  unfold periodicHypercubicEvenSpecialUnitaryRawTwoEndedWilsonAmplitude
  simpa using
    (periodicHypercubicEvenSpecialUnitaryProjectedKernelRightPhysicalCoefficient_integral_laterTail
      (h + 1) N hN beta hbeta f
      (fun laterTail => laterTail 0)
      (periodicHypercubicEvenSpecialUnitaryWilsonLaterTailEndpointRemainder h N beta g))

/-- Two-ended finite physical recursion in literal adjacent-slab form. -/
theorem periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_literal
    (h N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule (h + 1) N) :
    periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude
        h N hN beta hbeta f g =
      periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude h N beta f g := by
  rw [periodicHypercubicEvenSpecialUnitaryProjectedTwoEndedWilsonAmplitude_eq_raw]
  unfold periodicHypercubicEvenSpecialUnitaryRawTwoEndedWilsonAmplitude
  unfold periodicHypercubicEvenSpecialUnitaryLiteralTwoEndedWilsonAmplitude
  apply integral_congr_ae
  filter_upwards with laterTail
  unfold periodicHypercubicEvenSpecialUnitaryRawTwoSlabCoefficient
  unfold periodicHypercubicEvenSpecialUnitaryWilsonLaterTailEndpointRemainder
  rw [← MeasureTheory.integral_mul_const]
  apply integral_congr_ae
  filter_upwards with p
  rw [periodicHypercubicEvenSpecialUnitaryWilsonLaterTail_product_factor]
  ring

end

end MathlibAnalytic
end MGAP4D