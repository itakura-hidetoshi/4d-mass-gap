import MGAP4D.MathlibAnalytic.CompactGaugeWilsonHaarGibbsMeasure
import Mathlib.MeasureTheory.Integral.CompactlySupported

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal
open MeasureTheory Set

noncomputable section

/-- A compact-gauge Wilson system whose plaquette energy is continuous.
For standard Wilson actions on compact matrix groups this is the natural
finite-volume regularity package. -/
structure ContinuousCompactGaugeWilsonSystem where
  base : CompactGaugeWilsonSystem
  plaquetteEnergy_continuous : Continuous base.plaquetteEnergy

/-- Plaquette holonomy is continuous as a function of the link configuration. -/
theorem continuous_compact_gauge_plaquetteHolonomy
    (C : ContinuousCompactGaugeWilsonSystem)
    (p : C.base.Plaquette) :
    Continuous (fun A : C.base.Configuration =>
      C.base.plaquetteHolonomy A p) := by
  unfold CompactGaugeWilsonSystem.plaquetteHolonomy
  fun_prop

/-- The finite Wilson action is continuous. -/
theorem continuous_compact_gauge_wilsonAction
    (C : ContinuousCompactGaugeWilsonSystem) :
    Continuous C.base.wilsonAction := by
  unfold CompactGaugeWilsonSystem.wilsonAction
  apply continuous_finset_sum
  intro p _hp
  exact C.plaquetteEnergy_continuous.comp
    (continuous_compact_gauge_plaquetteHolonomy C p)

/-- The logarithmic Gibbs exponent is continuous. -/
theorem continuous_compact_gauge_gibbsExponent
    (C : ContinuousCompactGaugeWilsonSystem) :
    Continuous C.base.gibbsExponent := by
  unfold CompactGaugeWilsonSystem.gibbsExponent
  exact continuous_const.mul (continuous_compact_gauge_wilsonAction C)

/-- The Boltzmann factor is continuous. -/
theorem continuous_compact_gauge_boltzmannFactor
    (C : ContinuousCompactGaugeWilsonSystem) :
    Continuous (fun A : C.base.Configuration =>
      Real.exp (C.base.gibbsExponent A)) :=
  Real.continuous_exp.comp (continuous_compact_gauge_gibbsExponent C)

/-- On the compact finite-link configuration space, the continuous Boltzmann
factor is integrable with respect to product Haar probability measure. -/
theorem continuous_compact_gauge_boltzmannIntegrable
    (C : ContinuousCompactGaugeWilsonSystem) :
    Integrable
      (fun A : C.base.Configuration =>
        Real.exp (C.base.gibbsExponent A))
      C.base.configurationHaarMeasure := by
  exact
    (continuous_compact_gauge_boltzmannFactor C).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- The finite-volume Wilson Gibbs measure, now constructed without a separate
integrability input. -/
def ContinuousCompactGaugeWilsonSystem.gibbsMeasure
    (C : ContinuousCompactGaugeWilsonSystem) :
    Measure C.base.Configuration :=
  C.base.gibbsMeasure
    (continuous_compact_gauge_boltzmannIntegrable C)

/-- The automatically constructed Gibbs measure is a probability measure. -/
theorem continuous_compact_gauge_gibbsMeasure_isProbabilityMeasure
    (C : ContinuousCompactGaugeWilsonSystem) :
    IsProbabilityMeasure C.gibbsMeasure := by
  unfold ContinuousCompactGaugeWilsonSystem.gibbsMeasure
  exact compactGauge_gibbsMeasure_isProbabilityMeasure C.base
    (continuous_compact_gauge_boltzmannIntegrable C)

/-- The automatically constructed partition function is strictly positive. -/
theorem continuous_compact_gauge_partitionFunction_pos
    (C : ContinuousCompactGaugeWilsonSystem) :
    0 < C.base.partitionFunction :=
  compact_gauge_partitionFunction_pos C.base
    (continuous_compact_gauge_boltzmannIntegrable C)

/-- Density formula for the automatically constructed Gibbs measure. -/
theorem continuous_compact_gauge_gibbsMeasure_eq_withDensity
    (C : ContinuousCompactGaugeWilsonSystem) :
    C.gibbsMeasure =
      C.base.configurationHaarMeasure.withDensity
        (fun A => ENNReal.ofReal
          (Real.exp (C.base.gibbsExponent A) /
            C.base.partitionFunction)) := by
  unfold ContinuousCompactGaugeWilsonSystem.gibbsMeasure
  exact compact_gauge_gibbsMeasure_eq_withDensity C.base
    (continuous_compact_gauge_boltzmannIntegrable C)

/-- A finite-volume approximation family in which Boltzmann integrability is a
theorem derived from continuity and compactness rather than supplied as data. -/
structure ContinuousCompactGaugeWilsonApproximationFamily where
  index : Type
  system : index → ContinuousCompactGaugeWilsonSystem
  latticeSpacing : index → ℝ
  volumeScale : index → ℝ
  gaugeInvariantFiniteVolume : Prop
  gaugeInvariantFiniteVolume_proof : gaugeInvariantFiniteVolume
  finiteVolumeReflectionPositive : Prop
  finiteVolumeReflectionPositive_proof : finiteVolumeReflectionPositive
  finiteVolumeEuclideanCovariant : Prop
  finiteVolumeEuclideanCovariant_proof : finiteVolumeEuclideanCovariant

/-- Forgetful projection to the previous compact-gauge approximation family. -/
def ContinuousCompactGaugeWilsonApproximationFamily.toCompactFamily
    (F : ContinuousCompactGaugeWilsonApproximationFamily) :
    CompactGaugeWilsonApproximationFamily :=
  { index := F.index
    system := fun i => (F.system i).base
    latticeSpacing := F.latticeSpacing
    volumeScale := F.volumeScale
    boltzmannIntegrable := fun i =>
      continuous_compact_gauge_boltzmannIntegrable (F.system i)
    gaugeInvariantFiniteVolume := F.gaugeInvariantFiniteVolume
    gaugeInvariantFiniteVolume_proof := F.gaugeInvariantFiniteVolume_proof
    finiteVolumeReflectionPositive := F.finiteVolumeReflectionPositive
    finiteVolumeReflectionPositive_proof := F.finiteVolumeReflectionPositive_proof
    finiteVolumeEuclideanCovariant := F.finiteVolumeEuclideanCovariant
    finiteVolumeEuclideanCovariant_proof := F.finiteVolumeEuclideanCovariant_proof }

/-- Direct projection to the existing continuum finite-volume spine. -/
def ContinuousCompactGaugeWilsonApproximationFamily.toFiniteVolumeApproximation
    (F : ContinuousCompactGaugeWilsonApproximationFamily) :
    EuclideanYangMillsFiniteVolumeApproximation :=
  F.toCompactFamily.toFiniteVolumeApproximation

/-- Every finite-volume measure in the continuous compact-gauge family is a
probability measure. -/
theorem continuous_compact_gauge_wilson_family_probability_measure
    (F : ContinuousCompactGaugeWilsonApproximationFamily)
    (i : F.index) :
    IsProbabilityMeasure
      (F.toFiniteVolumeApproximation.finiteVolumeMeasure
        (show F.toFiniteVolumeApproximation.index from i)) := by
  exact compact_gauge_wilson_family_probability_measure F.toCompactFamily i

end

end MathlibAnalytic
end MGAP4D
