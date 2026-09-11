import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConfigurationHaarReflectionInvariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenWilsonActionReflection
import MGAP4D.MathlibAnalytic.PeriodicHypercubicTranslationInvariance

/-!
# Reflection invariance of the actual even-periodic `SU(N)` Wilson Gibbs law

The two finite ingredients are now independently available on the exact physical
configuration carrier:

* product normalized Haar is measure-preserving under physical configuration
  reflection;
* the standard even-periodic `SU(N)` Wilson action is exactly reflection
  invariant, including the orientation-reversing time--space plaquettes.

This file performs only the final tilted-measure step.  It transports the Haar
reflection symmetry through the invariant Wilson Gibbs exponent and exposes both
`MeasurePreserving` and pushforward forms of the finite Gibbs-law symmetry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance wilsonGibbsReflectionIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance wilsonGibbsReflectionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance wilsonGibbsReflectionSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance wilsonGibbsReflectionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance wilsonGibbsReflectionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The finite even-periodic `SU(N)` Wilson Gibbs probability law is exactly
measure-preserving under physical Euclidean time reflection. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbs_measurePreserving_reflection
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta) :
    MeasurePreserving
      (periodicHypercubicEvenConfigurationReflection H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  apply measurePreserving_tilted_of_invariant
  · exact
      periodicHypercubicEvenSpecialUnitary_configurationHaar_measurePreserving_reflection
        H N hN beta beta_nonneg
  · exact
      (continuous_compact_oriented_gibbsExponent
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg)).measurable
  · intro A
    unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
    exact congrArg
      (fun x : ℝ =>
        -(periodicHypercubicSpecialUnitaryWilsonSystem
            (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).base.beta * x)
      (periodicHypercubicSpecialUnitaryWilsonSystem_wilsonAction_reflection_invariant
        H N hN beta beta_nonneg A)
  · exact
      continuous_compact_oriented_boltzmannIntegrable
        (periodicHypercubicSpecialUnitaryWilsonSystem
          (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg)

/-- Pushforward form of finite-volume Wilson Gibbs reflection invariance. -/
theorem periodicHypercubicEvenSpecialUnitary_gibbs_map_reflection_eq_self
    (H N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (beta_nonneg : 0 ≤ beta) :
    Measure.map
      (periodicHypercubicEvenConfigurationReflection H)
      (periodicHypercubicSpecialUnitaryWilsonSystem
        (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure =
    (periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta beta_nonneg).gibbsMeasure :=
  (periodicHypercubicEvenSpecialUnitary_gibbs_measurePreserving_reflection
    H N hN beta beta_nonneg).map_eq

end
end MathlibAnalytic
end MGAP4D
