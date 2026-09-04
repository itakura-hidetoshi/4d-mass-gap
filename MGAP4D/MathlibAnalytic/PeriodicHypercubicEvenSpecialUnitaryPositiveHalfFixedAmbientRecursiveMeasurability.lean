import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientRecursiveMeasurabilityIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveMeasurabilityCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveMeasurabilitySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveMeasurabilityMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveMeasurabilityBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveMeasurabilitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The fixed-ambient recursive chain kernel is jointly measurable in its
ordered boundary pair and all remaining inward spatial slices.

The proof follows the same two-sided Markov recursion as the kernel itself.
The `R+2` step is especially important: the canonical endpoint-peel
measurable equivalence supplies the new inner pair and deeper chain, so no
proof-dependent reindexing enters the measurable recursion. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_measurable
    (H N : ℕ)
    (beta : ℝ) :
    ∀ R : ℕ,
      Measurable
        (fun p :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
          PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
            H N beta R p.1 p.2) := by
  intro R
  induction R using Nat.strong_induction_on with
  | h R ih =>
      cases R with
      | zero =>
          have hK :=
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
              H N beta).measurable
          simpa [
            periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel] using
            hK.comp measurable_fst
      | succ R =>
          cases R with
          | zero =>
              have hCenter :
                  Measurable
                    (fun p :
                      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
                        H 1 N => p.2 0) :=
                (measurable_pi_apply 0).comp measurable_snd
              have hInput :
                  Measurable
                    (fun p :
                      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
                        H 1 N =>
                      (p.1, (p.2 0, p.2 0))) :=
                measurable_fst.prodMk (hCenter.prodMk hCenter)
              simpa [
                periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel] using
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous
                  H N beta).measurable.comp hInput
          | succ R =>
              let e :=
                periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
                  H R N
              have hPeel :
                  Measurable
                    (fun p :
                      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
                        H (R + 2) N => e p.2) :=
                e.measurable.comp measurable_snd
              have hPairInput :
                  Measurable
                    (fun p :
                      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
                        H (R + 2) N =>
                      (p.1, (e p.2).1)) :=
                measurable_fst.prodMk (measurable_fst.comp hPeel)
              have hPair :
                  Measurable
                    (fun p :
                      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
                        H (R + 2) N =>
                      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
                        H N beta (p.1, (e p.2).1)) :=
                (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel_continuous
                  H N beta).measurable.comp hPairInput
              have hRest :
                  Measurable
                    (fun p :
                      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
                      PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath
                        H (R + 2) N =>
                      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
                        H N beta R (e p.2).1 (e p.2).2) := by
                exact (ih R (by omega)).comp hPeel
              simpa [e,
                periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel] using
                hPair.mul hRest

/-- For every fixed boundary pair, the recursive chain kernel is strongly
measurable as a function of the remaining inward chain. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_boundary_stronglyMeasurable
    (H R N : ℕ)
    (beta : ℝ)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    StronglyMeasurable
      (fun path :
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
          H N beta R boundary path) := by
  exact
    ((periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_measurable
      H N beta R).comp (measurable_const.prodMk measurable_id)).stronglyMeasurable

/-- The Haar-integrated fixed-ambient recursive message is strongly measurable
on the common pair-Haar carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_stronglyMeasurable
    (H R N : ℕ)
    (beta : ℝ) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H R N beta) := by
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
  exact
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_measurable
      H N beta R).stronglyMeasurable.integral_prod_right'

end

end MathlibAnalytic
end MGAP4D
