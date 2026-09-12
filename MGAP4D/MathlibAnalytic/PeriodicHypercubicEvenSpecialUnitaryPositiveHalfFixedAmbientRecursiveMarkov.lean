import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveMeasurability
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientRecursiveMarkovIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveMarkovCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveMarkovSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveMarkovMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveMarkovBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveMarkovSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The peeled pair-kernel times the shorter recursive chain kernel is
integrable on pair-Haar × deep-Haar.  The proof uses only joint measurability,
probability of the finite Haar product, and the pointwise Wilson bound by one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairKernel_mul_recursiveChainKernel_integrable
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, q.1) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
            H N beta R q.1 q.2)
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
        H R N) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
      H R N
  letI : IsFiniteMeasure μ := by infer_instance
  have hK :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).measurable
  have hLeftInput :
      Measurable
        (fun q :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
          (boundary.1, q.1.1)) :=
    measurable_const.prodMk (measurable_fst.comp measurable_fst)
  have hRightInput :
      Measurable
        (fun q :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
          (boundary.2, q.1.2)) :=
    measurable_const.prodMk (measurable_snd.comp measurable_fst)
  have hPair :
      Measurable
        (fun q :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, q.1)) := by
    simpa only [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel] using
      (hK.comp hLeftInput).mul (hK.comp hRightInput)
  have hRest :
      Measurable
        (fun q :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
            H N beta R q.1 q.2) :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_measurable
      H N beta R
  have hMeas :
      AEStronglyMeasurable
        (fun q :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
            PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (boundary, q.1) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
              H N beta R q.1 q.2)
        μ :=
    (hPair.mul hRest).stronglyMeasurable.aestronglyMeasurable
  have hInt : Integrable
      (fun q :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, q.1) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
            H N beta R q.1 q.2)
      μ := by
    exact Integrable.of_bound hMeas 1
      (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs, abs_mul]
        calc
          |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (boundary, q.1)| *
              |periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
                H N beta R q.1 q.2| ≤ 1 * 1 := by
            exact mul_le_mul
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_abs_le_one
                H N hN beta hbeta (boundary, q.1))
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_abs_le_one
                H N hN beta hbeta R q.1 q.2)
              (abs_nonneg _) (by norm_num)
          _ = 1 := by norm_num)
  simpa [μ] using hInt

/-- Exact fixed-ambient Markov/Fubini recursion for the Haar-integrated inward
message.  Peeling two remaining slices is one application of the ambient pair
kernel to the shorter message, with the ambient spatial carrier held fixed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_add_two_eq_pairKernel_message_integral
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H (R + 2) N beta boundary =
      ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta inner
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  let μPair :=
    periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let μDeep :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
      H R N
  have hInt :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairKernel_mul_recursiveChainKernel_integrable
      H R N hN beta hbeta boundary
  rw [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_add_two_eq_pairDeep]
  change
    (∫ q,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta (boundary, q.1) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
          H N beta R q.1 q.2
      ∂(μPair.prod μDeep)) = _
  calc
    (∫ q,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
          H N beta (boundary, q.1) *
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
          H N beta R q.1 q.2
      ∂(μPair.prod μDeep)) =
        ∫ inner, ∫ deep,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
              H N beta (boundary, inner) *
            periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
              H N beta R inner deep
          ∂μDeep ∂μPair := by
      exact MeasureTheory.integral_prod _
        (by
          simpa [μPair, μDeep,
            periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure]
            using hInt)
    _ = ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta inner
        ∂μPair := by
      apply integral_congr_ae
      filter_upwards with inner
      rw [integral_const_mul]
      rfl
    _ = ∫ inner,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, inner) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
            H R N beta inner
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
