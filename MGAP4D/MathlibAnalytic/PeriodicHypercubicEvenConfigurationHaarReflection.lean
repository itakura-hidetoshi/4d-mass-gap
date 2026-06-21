import MGAP4D.MathlibAnalytic.NormalizedCompactHaarInversion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryWilsonSystem
import Mathlib.MeasureTheory.Constructions.Pi

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Edge reflection as a finite index equivalence. -/
def periodicHypercubicEvenEdgeReflectionEquiv
    (H : ℕ) :
    PeriodicHypercubicEvenEdge H ≃ PeriodicHypercubicEvenEdge H :=
  (periodicHypercubicEvenEdgeReflection_involutive H).toPerm

@[simp]
theorem periodicHypercubicEvenEdgeReflectionEquiv_apply
    (H : ℕ) (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenEdgeReflectionEquiv H e =
      periodicHypercubicEvenEdgeReflection H e :=
  rfl

/-- Measurable reindexing of configurations by reflected physical links. -/
noncomputable def periodicHypercubicEvenConfigurationReindexMeasurableEquiv
    (H : ℕ) (Value : Type) [MeasurableSpace Value] :
    (PeriodicHypercubicEvenEdge H → Value) ≃ᵐ
      (PeriodicHypercubicEvenEdge H → Value) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : PeriodicHypercubicEvenEdge H => Value)
    (periodicHypercubicEvenEdgeReflectionEquiv H)

/-- Reflected-edge reindexing evaluates the original configuration at the
reflected link. -/
theorem periodicHypercubicEvenConfigurationReindexMeasurableEquiv_apply
    (H : ℕ) (Value : Type) [MeasurableSpace Value]
    (A : PeriodicHypercubicEvenEdge H → Value)
    (e : PeriodicHypercubicEvenEdge H) :
    periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Value A e =
      A (periodicHypercubicEvenEdgeReflection H e) := by
  simpa [periodicHypercubicEvenConfigurationReindexMeasurableEquiv,
    periodicHypercubicEvenEdgeReflectionEquiv,
    periodicHypercubicEvenEdgeReflection_involutive H e] using
    (MeasurableEquiv.piCongrLeft_apply_apply
      (β := fun _ : PeriodicHypercubicEvenEdge H => Value)
      (periodicHypercubicEvenEdgeReflectionEquiv H)
      A (periodicHypercubicEvenEdgeReflection H e))

/-- Reflected-edge reindexing preserves every constant finite product measure. -/
theorem periodicHypercubicEvenConfigurationReindex_measurePreserving
    (H : ℕ)
    {Value : Type} [MeasurableSpace Value]
    (μ : Measure Value) [SigmaFinite μ] :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Value)
      (Measure.pi (fun _ : PeriodicHypercubicEvenEdge H => μ))
      (Measure.pi (fun _ : PeriodicHypercubicEvenEdge H => μ)) := by
  simpa [periodicHypercubicEvenConfigurationReindexMeasurableEquiv] using
    (MeasureTheory.measurePreserving_piCongrLeft
      (fun _ : PeriodicHypercubicEvenEdge H => μ)
      (periodicHypercubicEvenEdgeReflectionEquiv H))

/-- Pointwise orientation correction after reflected-edge reindexing. -/
def periodicHypercubicEvenConfigurationOrientationCorrection
    {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenEdge H → Gauge :=
  fun e => if e.2 = 0 then (A e)⁻¹ else A e

end

end MathlibAnalytic
end MGAP4D
