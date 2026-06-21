import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenConfigurationHaarMeasureReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionReflection
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonGaugeInvariance
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Function Set

noncomputable section

/-- Canonical compact-topological and Borel receipts used while elaborating the
concrete `SU(N)` configuration measures below. -/
local instance periodicHypercubicGibbsSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance periodicHypercubicGibbsSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance periodicHypercubicGibbsSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance periodicHypercubicGibbsSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance periodicHypercubicGibbsSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

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

/-- Reflection invariance of every measurable finite-volume Wilson Gibbs event,
obtained by evaluating the pushforward equality on that event. -/
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
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure s :=
      (Measure.map_apply hMP.measurable hs).symm
    _ = _ := congrArg (fun μ : Measure _ => μ s) hMP.map_eq

/-- Every measurable finite-volume observable has the same Wilson Gibbs
pushforward law before and after physical time reflection. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_observable_law_invariant
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    {Y : Type} [MeasurableSpace Y]
    (O : (PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) → Y)
    (hO : Measurable O) :
    Measure.map
        (O ∘ periodicHypercubicEvenConfigurationReflection
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure =
      Measure.map O
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
  have hMP :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
      H N hN beta beta_nonneg
  calc
    Measure.map
        (O ∘ periodicHypercubicEvenConfigurationReflection
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure =
        Measure.map O
          (Measure.map
            (periodicHypercubicEvenConfigurationReflection
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
            (periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure) :=
      (Measure.map_map hO hMP.measurable).symm
    _ = Measure.map O
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
      exact congrArg (Measure.map O)
        (periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_map_eq_self
          H N hN beta beta_nonneg)

/-- Expectations of bounded continuous real observables under the actual
finite-volume Wilson Gibbs law are invariant under physical time reflection. -/
theorem periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_bounded_observable_expectation_invariant
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (O : BoundedContinuousFunction
      (PeriodicHypercubicEvenEdge H →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ℝ) :
    (∫ A, O (periodicHypercubicEvenConfigurationReflection H A)
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure) =
      ∫ A, O A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
  have hMP :=
    periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_measurePreserving
      H N hN beta beta_nonneg
  calc
    (∫ A, O (periodicHypercubicEvenConfigurationReflection H A)
      ∂(periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure) =
        ∫ A, O A
          ∂Measure.map
            (periodicHypercubicEvenConfigurationReflection
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) H)
            (periodicHypercubicSpecialUnitaryWilsonSystem
              (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
      symm
      exact MeasureTheory.integral_map
        hMP.measurable.aemeasurable
        O.continuous.aestronglyMeasurable
    _ = ∫ A, O A
        ∂(periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
      simpa only using congrArg
        (fun μ : Measure (PeriodicHypercubicEvenEdge H →
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
          ∫ A, O A ∂μ)
        (periodicHypercubicSpecialUnitaryWilsonSystem_gibbs_reflection_map_eq_self
          H N hN beta beta_nonneg)

end

end MathlibAnalytic
end MGAP4D
