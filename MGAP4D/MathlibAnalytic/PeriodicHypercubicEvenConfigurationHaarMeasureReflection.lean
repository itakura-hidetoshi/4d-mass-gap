import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarReflection

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Physical configuration reflection factors as reflected-edge reindexing
followed by the orientation correction that inverts time-link values. -/
theorem periodicHypercubicEvenConfigurationReflection_eq_orientationCorrection_reindex
    {Gauge : Type} [Group Gauge] [MeasurableSpace Gauge]
    (H : ℕ)
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenConfigurationReflection H A =
      periodicHypercubicEvenConfigurationOrientationCorrection
        (H := H)
        (periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Gauge A) := by
  funext e
  rw [periodicHypercubicEvenConfigurationReindexMeasurableEquiv_apply]
  rfl

/-- Physical even-periodic configuration reflection preserves product normalized
Haar probability for every compact topological gauge group. -/
theorem periodicHypercubicEvenConfigurationReflection_measurePreserving
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [TopologicalSpace Gauge]
    [IsTopologicalGroup Gauge] [CompactSpace Gauge]
    [MeasurableSpace Gauge] [BorelSpace Gauge] :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationReflection (Gauge := Gauge) H)
      (Measure.pi (fun _ : PeriodicHypercubicEvenEdge H =>
        normalizedCompactHaar Gauge))
      (Measure.pi (fun _ : PeriodicHypercubicEvenEdge H =>
        normalizedCompactHaar Gauge)) := by
  have hreindex :=
    periodicHypercubicEvenConfigurationReindex_measurePreserving H
      (normalizedCompactHaar Gauge)
  have horientation :=
    periodicHypercubicEvenConfigurationOrientationCorrection_measurePreserving
      H Gauge
  have hcomposition := horientation.comp hreindex
  have hfun :
      periodicHypercubicEvenConfigurationOrientationCorrection
          (H := H) (Gauge := Gauge) ∘
        periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Gauge =
      periodicHypercubicEvenConfigurationReflection H := by
    funext A
    exact
      (periodicHypercubicEvenConfigurationReflection_eq_orientationCorrection_reindex
        H A).symm
  rw [hfun] at hcomposition
  exact hcomposition

end

end MathlibAnalytic
end MGAP4D
