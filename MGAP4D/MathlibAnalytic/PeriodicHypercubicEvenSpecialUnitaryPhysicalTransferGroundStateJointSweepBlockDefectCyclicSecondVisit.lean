import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSweepBlockDefectVectorRenewal
import Mathlib.Tactic

/-!
# Cyclic second-visit identity for the positive-beta sweep obstruction

Let an ordered projection sweep be split at one label `e` as

  canonicalList = pre ++ e :: suffix.

The first visit to `e` occurs after `pre`.  After that visit, completing the
first sweep applies `suffix`; starting the second sweep applies `pre` before
`e` is visited again.  Therefore the operators acting between the two visits
to `e` are exactly

  suffix ++ pre.

This file proves that statement first for an arbitrary ordered family of
continuous linear maps, then specializes it to the genuine fixed-spatial-color
one-link conditional expectations.

Consequently the second-sweep residual at `e` is exactly the residual obtained
after propagating the first post-`e` vector through the cyclic between-visits
source-update order `suffix ++ pre`.

This is purely ordered algebra.  It uses no commutativity, response symmetry,
finite-cardinality estimate, factor two, or positivity assumption beyond the
parameters already present in the physical carrier.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Generic cyclic-between-visits identity.

If a sweep order is `pre ++ e :: suffix`, then applying the second-sweep
prefix `pre` to the terminal first-sweep vector is exactly the same as
applying the cyclic list `suffix ++ pre` to the vector immediately after
the first application of `e`. -/
theorem realHilbertProjectionSweep_secondVisitPrefix_eq_cyclicBetweenVisits
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (e : C)
    (x : E) :
    realHilbertProjectionSweep P pre
        (realHilbertProjectionSweep P (pre ++ e :: suffix) x) =
      realHilbertProjectionSweep P (suffix ++ pre)
        (P e (realHilbertProjectionSweep P pre x)) := by
  rw [
    realHilbertProjectionSweep_append P pre (e :: suffix) x,
    realHilbertProjectionSweep_append P suffix pre
      (P e (realHilbertProjectionSweep P pre x))]
  rfl

/-- Residual form of the generic cyclic-between-visits identity.

The residual created at the second visit to `e` is the `e`-projection
residual of the vector obtained by propagating the first post-`e` vector
through `suffix ++ pre`. -/
theorem realHilbertProjectionSweep_secondVisitResidual_eq_cyclicBetweenVisits
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (e : C)
    (x : E) :
    realHilbertProjectionSweep P pre
          (realHilbertProjectionSweep P (pre ++ e :: suffix) x) -
        P e
          (realHilbertProjectionSweep P pre
            (realHilbertProjectionSweep P (pre ++ e :: suffix) x)) =
      realHilbertProjectionSweep P (suffix ++ pre)
          (P e (realHilbertProjectionSweep P pre x)) -
        P e
          (realHilbertProjectionSweep P (suffix ++ pre)
            (P e (realHilbertProjectionSweep P pre x))) := by
  rw [
    realHilbertProjectionSweep_secondVisitPrefix_eq_cyclicBetweenVisits
      P pre suffix e x]

local instance sweepBlockDefectCyclicSecondVisitSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sweepBlockDefectCyclicSecondVisitSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Fixed-color specialization of the cyclic second-visit identity.

For a canonical split `pre ++ e :: suffix`, the vector immediately before the
second application of the one-link conditional expectation at `e` is exactly
the first post-`e` vector propagated through `suffix ++ pre`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondSweepStageVector_eq_cyclicBetweenVisits
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
        H N hN beta hbeta color pre
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
          H N hN beta hbeta color f) =
      realHilbertProjectionSweep
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        (suffix ++ pre)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color e
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color pre f)) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  have h :=
    realHilbertProjectionSweep_secondVisitPrefix_eq_cyclicBetweenVisits
      P pre suffix e f
  simpa [
    P,
    hSplit,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector] using h

/-- Fixed-color residual specialization.

The actual second-sweep stage residual at `e` is the target-`e` residual
after exactly the cyclic between-visits update order `suffix ++ pre`.
This is the exact target carrier to which the source-update response machinery
can be attached. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondSweepStageResidual_eq_cyclicBetweenVisits
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix :
      List (PeriodicHypercubicEvenFixedSpatialColorLink H color))
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hSplit :
      (Finset.univ :
        Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList =
          pre ++ e :: suffix) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color pre
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
            H N hN beta hbeta color f) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color e
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
            H N hN beta hbeta color pre
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector
              H N hN beta hbeta color f)) =
      realHilbertProjectionSweep
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          (suffix ++ pre)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color e
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta color pre f)) -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color e
          (realHilbertProjectionSweep
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color)
            (suffix ++ pre)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color e
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta color pre f))) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondSweepStageVector_eq_cyclicBetweenVisits
      H N hN beta hbeta color pre suffix e f hSplit]

end

end MGAP4D.MathlibAnalytic
