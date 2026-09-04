import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientRecursiveHaarMessageIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveHaarMessageCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveHaarMessageSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveHaarMessageMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveHaarMessageBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveHaarMessageSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Haar-integrated fixed-ambient inward message with `R` remaining interior
spatial slices.

Unlike the earlier `J_M`, the ambient spatial extent `H` is an independent
parameter.  Hence changing `R` keeps every message on the same ordered-pair
spatial carrier, which is the necessary type discipline for transfer-operator
iteration. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
    (H R N : ℕ)
    (beta : ℝ)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ path,
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
      H N beta R boundary path
    ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
      H R N)

/-- Exact non-Fubini recursion seam for the fixed-ambient inward message.

For `R+2` remaining slices, the fixed-ambient endpoint-peel equivalence
transports product Haar exactly to `pair-Haar × deep-Haar`.  In those
coordinates the recursive chain kernel is pointwise the pair one-step kernel
times the shorter recursive chain kernel.

This theorem performs only measure-preserving change of variables; no
interchange of integrals is used yet. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage_add_two_eq_pairDeep
    (H R N : ℕ)
    (beta : ℝ)
    (boundary :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
        H (R + 2) N beta boundary =
      ∫ q,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, q.1) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
            H N beta R q.1 q.2
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
          H R N) := by
  let e :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv
      H R N
  let F := fun q :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ×
        PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPath H R N =>
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
        H N beta (boundary, q.1) *
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
        H N beta R q.1 q.2
  unfold periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessage
  calc
    (∫ path,
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
        H N beta (R + 2) boundary path
      ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
        H (R + 2) N)) =
        ∫ path, F (e path)
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientInteriorSpatialPathHaarMeasure
            H (R + 2) N) := by
      apply integral_congr_ae
      filter_upwards with path
      simpa [F, e] using
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel_add_two
          H R N beta boundary path)
    _ = ∫ q, F q
          ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
            H R N) := by
      exact
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairPeelMeasurableEquiv_measurePreserving
          H R N).integral_comp' F
    _ = ∫ q,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairKernel
            H N beta (boundary, q.1) *
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveChainKernel
            H N beta R q.1 q.2
        ∂(periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientPairDeepSpatialHaarMeasure
          H R N) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
