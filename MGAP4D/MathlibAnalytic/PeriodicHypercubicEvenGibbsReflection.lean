import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarMeasureReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionReflection
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonGaugeInvariance

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- The actual even-periodic `SU(N)` Wilson Gibbs exponent is invariant under
physical time reflection of positive-link configurations. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbsExponent_reflection_invariant
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.gibbsExponent
      (periodicHypercubicEvenConfigurationReflection H A) =
    (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.gibbsExponent A := by
  unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
  rw [periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_reflection_invariant]

/-- The actual finite-volume even-periodic `SU(N)` Wilson Gibbs probability law
is invariant under physical time reflection. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationReflection
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
  let C := periodicHypercubicSpecialUnitaryWilsonSystem
    (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg
  change MeasurePreserving
    (periodicHypercubicEvenConfigurationReflection
      (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
    C.gibbsMeasure C.gibbsMeasure
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  apply measurePreserving_tilted_of_invariant
  · simpa [C] using
      periodicHypercubicSpecialUnitaryWilsonSystem_configurationHaar_reflection_measurePreserving
        H N hN beta beta_nonneg
  · exact (continuous_compact_oriented_gibbsExponent C).measurable
  · intro A
    simpa [C] using
      periodicHypercubicSpecialUnitaryWilsonSystem_gibbsExponent_reflection_invariant
        H N hN beta beta_nonneg A
  · exact continuous_compact_oriented_boltzmannIntegrable C

/-- Pushforward form of finite-volume Wilson Gibbs reflection invariance. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_map_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) :
    Measure.map
      (periodicHypercubicEvenConfigurationReflection
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure =
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure :=
  (periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
    H N hN beta beta_nonneg).map_eq

/-- Reflection invariance of every measurable finite-volume Wilson Gibbs event. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_preimage_eq
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    {s : Set (PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ)}
    (hs : MeasurableSet s) :
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure
        ((periodicHypercubicEvenConfigurationReflection
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H) ⁻¹' s) =
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure s := by
  have hMP :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
      H N hN beta beta_nonneg
  calc
    _ = Measure.map
        (periodicHypercubicEvenConfigurationReflection
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure s := by
          rw [Measure.map_apply hMP.measurable hs]
    _ = _ := by rw [hMP.map_eq]

end

end MathlibAnalytic
end MGAP4D
