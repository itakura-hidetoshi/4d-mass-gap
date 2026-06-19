import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonHaarGibbsMeasure
import Mathlib.MeasureTheory.Integral.CompactlySupported

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Compact oriented Wilson data with continuous plaquette energy. -/
structure ContinuousCompactOrientedGaugeWilsonSystem where
  base : CompactOrientedGaugeWilsonSystem
  plaquetteEnergy_continuous : Continuous base.plaquetteEnergy

instance compactOriented_configuration_opensMeasurableSpace
    (L : CompactOrientedGaugeWilsonSystem) :
    OpensMeasurableSpace L.Configuration := by
  infer_instance

/-- Evaluation of one signed boundary incidence is continuous. -/
theorem continuous_compact_oriented_stepValue
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (step : FiniteOrientedBoundaryStep C.base.geometry.Edge) :
    Continuous (fun A : C.base.Configuration => C.base.stepValue A step) := by
  cases step with
  | mk edge orientation =>
      cases orientation <;>
        simp [CompactOrientedGaugeWilsonSystem.stepValue,
          FiniteOrientedFourDimensionalPlaquetteGeometry.stepValue] <;>
        fun_prop

/-- Signed plaquette holonomy is continuous on the physical-link configuration
space. -/
theorem continuous_compact_oriented_plaquetteHolonomy
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (p : C.base.geometry.Plaquette) :
    Continuous (fun A : C.base.Configuration =>
      C.base.plaquetteHolonomy A p) := by
  change Continuous (fun A : C.base.Configuration =>
    C.base.stepValue A (C.base.geometry.boundary p 0) *
      C.base.stepValue A (C.base.geometry.boundary p 1) *
      C.base.stepValue A (C.base.geometry.boundary p 2) *
      C.base.stepValue A (C.base.geometry.boundary p 3))
  exact
    (((continuous_compact_oriented_stepValue C
          (C.base.geometry.boundary p 0)).mul
        (continuous_compact_oriented_stepValue C
          (C.base.geometry.boundary p 1))).mul
      (continuous_compact_oriented_stepValue C
        (C.base.geometry.boundary p 2))).mul
    (continuous_compact_oriented_stepValue C
      (C.base.geometry.boundary p 3))

/-- The finite oriented Wilson action is continuous. -/
theorem continuous_compact_oriented_wilsonAction
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Continuous C.base.wilsonAction := by
  unfold CompactOrientedGaugeWilsonSystem.wilsonAction
  apply continuous_finset_sum
  intro p _hp
  exact C.plaquetteEnergy_continuous.comp
    (continuous_compact_oriented_plaquetteHolonomy C p)

/-- The oriented Gibbs exponent is continuous. -/
theorem continuous_compact_oriented_gibbsExponent
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Continuous C.base.gibbsExponent := by
  unfold CompactOrientedGaugeWilsonSystem.gibbsExponent
  exact continuous_const.mul (continuous_compact_oriented_wilsonAction C)

/-- The oriented Boltzmann factor is continuous. -/
theorem continuous_compact_oriented_boltzmannFactor
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Continuous (fun A : C.base.Configuration =>
      Real.exp (C.base.gibbsExponent A)) :=
  Real.continuous_exp.comp (continuous_compact_oriented_gibbsExponent C)

/-- Compactness of the finite physical-link configuration space gives automatic
Boltzmann integrability. -/
theorem continuous_compact_oriented_boltzmannIntegrable
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Integrable
      (fun A : C.base.Configuration =>
        Real.exp (C.base.gibbsExponent A))
      C.base.configurationHaarMeasure := by
  letI : OpensMeasurableSpace C.base.Configuration :=
    compactOriented_configuration_opensMeasurableSpace C.base
  exact
    (continuous_compact_oriented_boltzmannFactor C).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Canonical finite-volume Gibbs probability measure. -/
def ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Measure C.base.Configuration :=
  C.base.gibbsMeasure (continuous_compact_oriented_boltzmannIntegrable C)

/-- The canonical oriented Gibbs measure is a probability measure. -/
theorem continuous_compact_oriented_gibbsMeasure_isProbabilityMeasure
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    IsProbabilityMeasure C.gibbsMeasure := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.gibbsMeasure
  exact compactOriented_gibbsMeasure_isProbabilityMeasure C.base
    (continuous_compact_oriented_boltzmannIntegrable C)

end

end MathlibAnalytic
end MGAP4D
