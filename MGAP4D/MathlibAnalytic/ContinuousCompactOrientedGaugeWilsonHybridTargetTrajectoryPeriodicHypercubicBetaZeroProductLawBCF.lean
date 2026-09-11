import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanFrontierBCF
import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonSingleLinkHaarFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- At zero Wilson coupling, the global Gibbs exponent vanishes pointwise. -/
theorem continuous_compact_oriented_gibbsExponent_eq_zero_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (A : C.base.Configuration) :
    C.base.gibbsExponent A = 0 := by
  simp [CompactOrientedGaugeWilsonSystem.gibbsExponent, hBeta]

/-- At zero coupling, the global Boltzmann factor is identically one. -/
theorem continuous_compact_oriented_boltzmannFactor_eq_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (A : C.base.Configuration) :
    Real.exp (C.base.gibbsExponent A) = 1 := by
  rw [continuous_compact_oriented_gibbsExponent_eq_zero_of_beta_eq_zero C hBeta A]
  simp

/-- The zero-coupling finite-volume partition function is exactly one. -/
theorem continuous_compact_oriented_partitionFunction_eq_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0) :
    C.base.partitionFunction = 1 := by
  unfold CompactOrientedGaugeWilsonSystem.partitionFunction
  simp_rw [continuous_compact_oriented_boltzmannFactor_eq_one_of_beta_eq_zero C hBeta]
  simp

/-- At zero coupling, the canonical Gibbs probability law is exactly the product
normalized Haar measure on the physical positive-link configuration space. -/
theorem continuous_compact_oriented_gibbsMeasure_eq_configurationHaarMeasure_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0) :
    C.gibbsMeasure = C.base.configurationHaarMeasure := by
  have hExponent : C.base.gibbsExponent = 0 := by
    funext A
    exact continuous_compact_oriented_gibbsExponent_eq_zero_of_beta_eq_zero
      C hBeta A
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
    CompactOrientedGaugeWilsonSystem.gibbsMeasure
  rw [hExponent]
  exact MeasureTheory.tilted_zero C.base.configurationHaarMeasure

/-- At zero coupling, every one-link Boltzmann factor is identically one,
independently of the background and inserted group element. -/
theorem continuous_compact_oriented_singleLinkBoltzmannFactor_eq_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge)
    (g : C.base.Gauge) :
    C.singleLinkBoltzmannFactor A target g = 1 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkBoltzmannFactor
  rw [continuous_compact_oriented_gibbsExponent_eq_zero_of_beta_eq_zero
    C hBeta (C.base.replaceLink A target g)]
  simp

/-- The zero-coupling one-link conditional partition function is exactly one. -/
theorem continuous_compact_oriented_singleLinkPartitionFunction_eq_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkPartitionFunction A target = 1 := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkPartitionFunction
  simp_rw [continuous_compact_oriented_singleLinkBoltzmannFactor_eq_one_of_beta_eq_zero
    C hBeta A target]
  simp

/-- At zero coupling, every exact one-link conditional law is the same normalized
Haar law; it has no dependence on the off-link background. -/
theorem continuous_compact_oriented_singleLinkConditionalMeasure_eq_normalizedCompactHaar_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (A : C.base.Configuration)
    (target : C.base.geometry.Edge) :
    C.singleLinkConditionalMeasure A target =
      normalizedCompactHaar C.base.Gauge := by
  have hExponent :
      (fun g : C.base.Gauge =>
        C.base.gibbsExponent (C.base.replaceLink A target g)) = 0 := by
    funext g
    exact continuous_compact_oriented_gibbsExponent_eq_zero_of_beta_eq_zero
      C hBeta (C.base.replaceLink A target g)
  unfold ContinuousCompactOrientedGaugeWilsonSystem.singleLinkConditionalMeasure
  rw [hExponent]
  exact MeasureTheory.tilted_zero (normalizedCompactHaar C.base.Gauge)

/-- The actual endpoint system is exactly at zero Wilson coupling. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.beta = 0 := by
  rfl

/-- The actual side-three periodic `SU(2)` Gibbs law is the independent product
normalized Haar law on its `324` physical links. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gibbsMeasure_eq_configurationHaarMeasure :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure := by
  exact
    continuous_compact_oriented_gibbsMeasure_eq_configurationHaarMeasure_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero

/-- Every actual one-link conditional law is the normalized Haar law, uniformly
in the background configuration and target physical link. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkConditionalMeasure_eq_normalizedCompactHaar
    (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration)
    (target : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkConditionalMeasure
        A target =
      normalizedCompactHaar
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge := by
  exact
    continuous_compact_oriented_singleLinkConditionalMeasure_eq_normalizedCompactHaar_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
      A target

/-- Under the canonical selected-link/off-link coordinate equivalence, the actual
zero-coupling Gibbs law factors exactly as selected-link Haar times off-link
product Haar. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_map_canonicalSingleLinkCoordinates_gibbsMeasure
    (target : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    Measure.map
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.canonicalSingleLinkCoordinatesMeasurableEquiv
          target)
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =
      (normalizedCompactHaar
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge).prod
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.offLinkHaarMeasure
          target) := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gibbsMeasure_eq_configurationHaarMeasure]
  exact
    compact_oriented_map_canonicalSingleLinkCoordinates_configurationHaarMeasure
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base target

/-- Compact proof-facing receipt for the actual zero-coupling product-law layer.
This is the measure-theoretic input immediately preceding product-measure
variance tensorization; no Poincare inequality is asserted here. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroProductLawReceipt : Prop :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.configurationHaarMeasure ∧
    (∀ (A : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Configuration)
      (target : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge),
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkConditionalMeasure
          A target =
        normalizedCompactHaar
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge) ∧
    (∀ target : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
      Measure.map
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.canonicalSingleLinkCoordinatesMeasurableEquiv
            target)
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =
        (normalizedCompactHaar
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.Gauge).prod
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.offLinkHaarMeasure
            target))

/-- The actual endpoint Gibbs system satisfies the exact beta-zero product-law
receipt. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroProductLawReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroProductLawReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_gibbsMeasure_eq_configurationHaarMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_singleLinkConditionalMeasure_eq_normalizedCompactHaar,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_map_canonicalSingleLinkCoordinates_gibbsMeasure⟩

end

end MathlibAnalytic
end MGAP4D
