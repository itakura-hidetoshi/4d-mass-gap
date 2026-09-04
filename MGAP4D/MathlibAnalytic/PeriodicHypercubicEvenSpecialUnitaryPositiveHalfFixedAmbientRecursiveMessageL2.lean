import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveMarkov
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientRecursiveMessageL2IsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveMessageL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveMessageL2SecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveMessageL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveMessageL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveMessageL2SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every fixed-ambient recursive Haar message is pointwise bounded by one.
The remaining-chain Haar law is a probability measure and the recursive Wilson
chain kernel is itself pointwise bounded by one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_abs_le_one
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    |periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H R N beta boundary| ≤ 1 := by
  let μDeep :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
      H R N
  letI : IsFiniteMeasure μDeep := by infer_instance
  have h := norm_integral_le_of_norm_le_const
    (μ := μDeep)
    (f := fun path =>
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
        H N beta R boundary path)
    (C := 1)
    (Filter.Eventually.of_forall fun path => by
      simpa [Real.norm_eq_abs] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_abs_le_one
          H N hN beta hbeta R boundary path)
  simpa [
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage,
    μDeep, Real.norm_eq_abs] using h

/-- Every fixed-ambient recursive Haar message belongs to the common pair-Haar
`L²` carrier.  Crucially, the carrier depends on ambient `H` but not on the
remaining recursion length `R`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_memLp_two
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H R N beta)
      2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  exact MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_stronglyMeasurable
      H R N beta).aestronglyMeasurable
    1
    (Filter.Eventually.of_forall fun boundary => by
      simpa [Real.norm_eq_abs] using
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_abs_le_one
          H R N hN beta hbeta boundary)

/-- Canonical pair-Haar `L²` vector represented by the fixed-ambient recursive
Haar message. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    Lp ℝ 2
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_memLp_two
    H R N hN beta hbeta).toLp
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H R N beta)

/-- The canonical `L²` vector has the literal recursive Haar message as its
a.e. representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_coeFn
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (fun boundary =>
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta boundary) =ᵐ[
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H R N beta :=
  (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_memLp_two
    H R N hN beta hbeta).coeFn_toLp

end

end MathlibAnalytic
end MGAP4D
