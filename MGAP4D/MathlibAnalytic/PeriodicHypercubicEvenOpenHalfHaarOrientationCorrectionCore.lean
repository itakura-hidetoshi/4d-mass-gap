import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenBoundaryFiberedConfigurationReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarReflection

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Each positive-representative open-half coordinate is preserved by its
orientation correction: inversion on time links and identity on spatial links. -/
theorem periodicHypercubicEvenOpenHalfOrientationCorrection_coordinate_measurePreserving
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge]
    (e : (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge) :
    MeasurePreserving
      (fun x : Gauge => if e.1.2 = 0 then x⁻¹ else x)
      (normalizedCompactHaar Gauge) (normalizedCompactHaar Gauge) := by
  simpa using
    periodicHypercubicEvenOrientationCorrection_coordinate_measurePreserving
      H Gauge e.1

/-- Orientation correction on the selected positive representatives preserves the
canonical open-half product normalized Haar measure. -/
theorem periodicHypercubicEvenOpenHalfOrientationCorrection_measurePreserving
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge] :
    MeasurePreserving
      (periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge))
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar Gauge))
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar Gauge)) := by
  unfold FiniteInvolutiveEdgeOrbitPartition.openHalfPiMeasure
  refine ⟨?_, ?_⟩
  · unfold periodicHypercubicEvenOpenHalfOrientationCorrection
    refine measurable_pi_lambda _ ?_
    intro e
    exact
      (periodicHypercubicEvenOpenHalfOrientationCorrection_coordinate_measurePreserving
        H Gauge e).measurable.comp (measurable_pi_apply e)
  · let f :
        (periodicHypercubicEvenEdgeOrbitPartition H).PositiveEdge → Gauge → Gauge :=
      fun e x => if e.1.2 = 0 then x⁻¹ else x
    have hf : ∀ e,
        AEMeasurable (f e) (normalizedCompactHaar Gauge) :=
      fun e =>
        (periodicHypercubicEvenOpenHalfOrientationCorrection_coordinate_measurePreserving
          H Gauge e).measurable.aemeasurable
    letI : ∀ e, SigmaFinite
        ((normalizedCompactHaar Gauge).map (f e)) := fun e => by
      rw [(periodicHypercubicEvenOpenHalfOrientationCorrection_coordinate_measurePreserving
        H Gauge e).map_eq]
      infer_instance
    rw [show periodicHypercubicEvenOpenHalfOrientationCorrection
        (H := H) (Gauge := Gauge) =
      (fun A e => f e (A e)) by rfl]
    rw [Measure.pi_map_pi hf]
    congr 1
    funext e
    exact
      (periodicHypercubicEvenOpenHalfOrientationCorrection_coordinate_measurePreserving
        H Gauge e).map_eq

/-- The open-half orientation correction as a measurable involutive equivalence. -/
noncomputable def periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge] :
    (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge ≃ᵐ
      (periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration Gauge where
  toEquiv :=
    { toFun := periodicHypercubicEvenOpenHalfOrientationCorrection H
      invFun := periodicHypercubicEvenOpenHalfOrientationCorrection H
      left_inv := periodicHypercubicEvenOpenHalfOrientationCorrection_involutive H
      right_inv := periodicHypercubicEvenOpenHalfOrientationCorrection_involutive H }
  measurable_toFun :=
    (periodicHypercubicEvenOpenHalfOrientationCorrection_measurePreserving
      H Gauge).measurable
  measurable_invFun :=
    (periodicHypercubicEvenOpenHalfOrientationCorrection_measurePreserving
      H Gauge).measurable

/-- The measurable orientation-correction equivalence preserves open-half Haar
measure. -/
theorem periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv_measurePreserving
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge] :
    MeasurePreserving
      (periodicHypercubicEvenOpenHalfOrientationCorrectionMeasurableEquiv H Gauge)
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar Gauge))
      ((periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
        (normalizedCompactHaar Gauge)) := by
  exact periodicHypercubicEvenOpenHalfOrientationCorrection_measurePreserving H Gauge

end

end MathlibAnalytic
end MGAP4D
