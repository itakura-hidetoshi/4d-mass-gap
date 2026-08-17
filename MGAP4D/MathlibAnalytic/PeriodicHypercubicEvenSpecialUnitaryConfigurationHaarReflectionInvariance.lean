import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarReflection
import MGAP4D.MathlibAnalytic.SpecialUnitaryTopologicalCompactReceipts

/-!
# Full product-Haar invariance under physical configuration reflection

The component measure-preserving statements already exist:

* reflected-edge reindexing preserves every constant finite product measure;
* time-link orientation correction preserves product normalized compact Haar.

This file only identifies the physical positive-link configuration reflection as
that composition and packages the resulting full measure-preserving theorem,
then specializes it to the actual periodic `SU(N)` Wilson configuration Haar law.

Wilson-action and Gibbs reflection invariance remain separate downstream steps.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance configurationHaarReflectionFinalIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance configurationHaarReflectionFinalCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance configurationHaarReflectionFinalSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance configurationHaarReflectionFinalMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance configurationHaarReflectionFinalBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Physical positive-link reflection is reflected-edge reindexing followed by
the already defined time-link orientation correction. -/
theorem periodicHypercubicEvenConfigurationReflection_eq_orientationCorrection_comp_reindex
    (H : ℕ)
    (Gauge : Type) [Group Gauge] [MeasurableSpace Gauge]
    (A : PeriodicHypercubicEvenEdge H → Gauge) :
    periodicHypercubicEvenConfigurationReflection H A =
      periodicHypercubicEvenConfigurationOrientationCorrection
        (periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Gauge A) := by
  funext e
  by_cases htime : e.2 = 0 <;>
    simp [periodicHypercubicEvenConfigurationReflection,
      periodicHypercubicEvenConfigurationOrientationCorrection,
      periodicHypercubicEvenConfigurationReindexMeasurableEquiv_apply,
      htime]

/-- Full physical configuration reflection preserves the product normalized
compact Haar probability measure. -/
theorem periodicHypercubicEvenConfigurationReflection_measurePreserving_normalizedCompactHaar
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
  let μ : Measure (PeriodicHypercubicEvenEdge H → Gauge) :=
    Measure.pi (fun _ : PeriodicHypercubicEvenEdge H => normalizedCompactHaar Gauge)
  have hReindex :
      MeasurePreserving
        (periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Gauge)
        μ μ := by
    simpa [μ] using
      periodicHypercubicEvenConfigurationReindex_measurePreserving
        H (normalizedCompactHaar Gauge)
  have hOrientation :
      MeasurePreserving
        (periodicHypercubicEvenConfigurationOrientationCorrection
          (H := H) (Gauge := Gauge))
        μ μ := by
    simpa [μ] using
      periodicHypercubicEvenConfigurationOrientationCorrection_measurePreserving
        H Gauge
  have hreflect :
      periodicHypercubicEvenConfigurationReflection (Gauge := Gauge) H =
        periodicHypercubicEvenConfigurationOrientationCorrection ∘
          periodicHypercubicEvenConfigurationReindexMeasurableEquiv H Gauge := by
    funext A
    exact
      periodicHypercubicEvenConfigurationReflection_eq_orientationCorrection_comp_reindex
        H Gauge A
  refine ⟨?_, ?_⟩
  · rw [hreflect]
    exact hOrientation.measurable.comp hReindex.measurable
  · rw [hreflect]
    rw [← Measure.map_map hOrientation.measurable hReindex.measurable]
    rw [hReindex.map_eq, hOrientation.map_eq]

/-- The actual even-periodic `SU(N)` Wilson reference Haar law is preserved by
physical Euclidean time reflection. -/
theorem periodicHypercubicEvenSpecialUnitary_configurationHaar_measurePreserving_reflection
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationReflection H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure := by
  unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
  exact
    periodicHypercubicEvenConfigurationReflection_measurePreserving_normalizedCompactHaar
      H (Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Pushforward form of the same finite configuration-Haar reflection invariance. -/
theorem periodicHypercubicEvenSpecialUnitary_configurationHaar_map_reflection_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map
      (periodicHypercubicEvenConfigurationReflection H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure =
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta hbeta).base.configurationHaarMeasure :=
  (periodicHypercubicEvenSpecialUnitary_configurationHaar_measurePreserving_reflection
    H N hN beta hbeta).map_eq

end
end MathlibAnalytic
end MGAP4D
