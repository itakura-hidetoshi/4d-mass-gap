import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkHaarCoordinateSplit
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The selected-link subtype has exactly one point, namely the selected target.
This instance is kept local so the canonical target carrier remains the literal
subtype used by the existing Haar-coordinate split. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- Evaluation at the unique selected link is a measurable equivalence from the
canonical singleton-target configuration carrier to the direct gauge-group
carrier.

This is an explicit carrier bridge.  It does not identify any ground-state
fiber measure with a Wilson conditional law. -/
noncomputable def periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpatialSliceTargetLink H target → Gauge) ≃ᵐ Gauge :=
  MeasurableEquiv.funUnique
    (PeriodicHypercubicEvenSpatialSliceTargetLink H target) Gauge

/-- The direct target-coordinate bridge carries the singleton product measure
exactly to the underlying one-coordinate measure. -/
theorem periodicHypercubicEvenSpatialSliceTargetEvaluation_measurePreserving
    {H : ℕ}
    {Gauge : Type}
    [MeasurableSpace Gauge]
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (μ : Measure Gauge) :
    MeasurePreserving
      (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
        (Gauge := Gauge) target)
      (Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target => μ))
      μ := by
  simpa [periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv] using
    (measurePreserving_funUnique μ
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target))

end

end MathlibAnalytic
end MGAP4D
