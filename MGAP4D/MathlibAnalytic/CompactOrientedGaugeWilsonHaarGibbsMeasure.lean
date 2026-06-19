import MGAP4D.MathlibAnalytic.CompactOrientedGaugeWilsonAction

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

/-- Product normalized Haar measure on physical positive-link configurations. -/
def CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
    (L : CompactOrientedGaugeWilsonSystem) : Measure L.Configuration :=
  Measure.pi (fun _ : L.geometry.Edge => normalizedCompactHaar L.Gauge)

instance compactOriented_configurationHaar_isProbabilityMeasure
    (L : CompactOrientedGaugeWilsonSystem) :
    IsProbabilityMeasure L.configurationHaarMeasure := by
  unfold CompactOrientedGaugeWilsonSystem.configurationHaarMeasure
  infer_instance

/-- Logarithmic Wilson Gibbs weight. -/
def CompactOrientedGaugeWilsonSystem.gibbsExponent
    (L : CompactOrientedGaugeWilsonSystem)
    (A : L.Configuration) : ℝ :=
  -L.beta * L.wilsonAction A

/-- Gauge invariance of the Gibbs exponent. -/
theorem compact_oriented_gibbsExponent_gaugeInvariant
    (L : CompactOrientedGaugeWilsonSystem)
    (gamma : L.GaugeTransformation)
    (A : L.Configuration) :
    L.gibbsExponent (L.gaugeTransform gamma A) = L.gibbsExponent A := by
  simp only [CompactOrientedGaugeWilsonSystem.gibbsExponent]
  rw [compact_oriented_wilsonAction_gaugeInvariant]

/-- Real partition function with respect to product Haar probability. -/
def CompactOrientedGaugeWilsonSystem.partitionFunction
    (L : CompactOrientedGaugeWilsonSystem) : ℝ :=
  ∫ A, Real.exp (L.gibbsExponent A) ∂L.configurationHaarMeasure

/-- Finite-volume oriented Wilson Gibbs measure. -/
def CompactOrientedGaugeWilsonSystem.gibbsMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (_hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) : Measure L.Configuration :=
  L.configurationHaarMeasure.tilted L.gibbsExponent

/-- The oriented compact-gauge Gibbs measure is a probability measure. -/
theorem compactOriented_gibbsMeasure_isProbabilityMeasure
    (L : CompactOrientedGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    IsProbabilityMeasure (L.gibbsMeasure hIntegrable) := by
  unfold CompactOrientedGaugeWilsonSystem.gibbsMeasure
  exact MeasureTheory.isProbabilityMeasure_tilted hIntegrable

/-- Positivity of the oriented finite-volume partition function. -/
theorem compact_oriented_partitionFunction_pos
    (L : CompactOrientedGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    0 < L.partitionFunction := by
  unfold CompactOrientedGaugeWilsonSystem.partitionFunction
  exact integral_exp_pos hIntegrable

/-- Density formula for the oriented compact-gauge Gibbs measure. -/
theorem compact_oriented_gibbsMeasure_eq_withDensity
    (L : CompactOrientedGaugeWilsonSystem)
    (hIntegrable : Integrable
      (fun A => Real.exp (L.gibbsExponent A))
      L.configurationHaarMeasure) :
    L.gibbsMeasure hIntegrable =
      L.configurationHaarMeasure.withDensity
        (fun A => ENNReal.ofReal
          (Real.exp (L.gibbsExponent A) / L.partitionFunction)) := by
  rfl

end

end MathlibAnalytic
end MGAP4D
