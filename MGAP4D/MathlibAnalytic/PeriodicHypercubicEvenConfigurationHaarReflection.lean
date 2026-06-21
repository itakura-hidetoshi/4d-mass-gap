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
    {H : ℕ} {Gauge : Type} [Group Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    PeriodicHypercubicEvenEdge H → Gauge :=
  fun e => if e.2 = 0 then (A e)⁻¹ else A e

/-- Each coordinate of orientation correction preserves normalized compact
Haar probability: inversion on time links and identity on spatial links. -/
theorem periodicHypercubicEvenOrientationCorrection_coordinate_measurePreserving
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge]
    (e : PeriodicHypercubicEvenEdge H) :
    MeasurePreserving
      (fun x : Gauge => if e.2 = 0 then x⁻¹ else x)
      (normalizedCompactHaar Gauge) (normalizedCompactHaar Gauge) := by
  by_cases htime : e.2 = 0
  · simpa [htime] using normalizedCompactHaar_measurePreserving_inv Gauge
  · simpa [htime] using
      (MeasurePreserving.id (normalizedCompactHaar Gauge))

/-- Orientation correction preserves product normalized Haar measure. -/
theorem periodicHypercubicEvenConfigurationOrientationCorrection_measurePreserving
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge] :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationOrientationCorrection
        (H := H) (Gauge := Gauge))
      (Measure.pi (fun _ : PeriodicHypercubicEvenEdge H =>
        normalizedCompactHaar Gauge))
      (Measure.pi (fun _ : PeriodicHypercubicEvenEdge H =>
        normalizedCompactHaar Gauge)) := by
  refine ⟨?_, ?_⟩
  · unfold periodicHypercubicEvenConfigurationOrientationCorrection
    fun_prop
  · let f : PeriodicHypercubicEvenEdge H → Gauge → Gauge :=
      fun e x => if e.2 = 0 then x⁻¹ else x
    have hf : ∀ e,
        AEMeasurable (f e) (normalizedCompactHaar Gauge) :=
      fun e =>
        (periodicHypercubicEvenOrientationCorrection_coordinate_measurePreserving
          H Gauge e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite
        ((normalizedCompactHaar Gauge).map (f e)) := fun e => by
      rw [(periodicHypercubicEvenOrientationCorrection_coordinate_measurePreserving
        H Gauge e).map_eq]
      infer_instance
    rw [show periodicHypercubicEvenConfigurationOrientationCorrection
        (H := H) (Gauge := Gauge) =
      (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (periodicHypercubicEvenOrientationCorrection_coordinate_measurePreserving
        H Gauge e).map_eq

end

end MathlibAnalytic
end MGAP4D
