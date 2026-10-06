import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousGroundStateFiberPosteriorMeasureBridge

/-! Regression contracts for the genuine-fiber / posterior bridge. -/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal

example {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [NeZero μ]
    (f : α → ℝ) (hf : Integrable (fun x => Real.exp (f x)) μ)
    (c : ℝ) (hc : 0 < c) :
    doobWeightedMeasure μ (fun x => ENNReal.ofReal (c * Real.exp (f x))) =
      μ.tilted f := by
  exact doobWeightedMeasure_ofReal_mul_exp_eq_tilted μ f hf c hc

#check GroundStatePosteriorFiberBridge.continuousCompatible_eq_posterior
#check GroundStatePosteriorFiberBridge.normalizedFiberMeasure_ae_eq_posterior
#check GroundStatePosteriorFiberBridge.fiberIntegral_ae_eq_posteriorConditionalExpectation

#print axioms doobWeightedMeasure_ofReal_mul_exp_eq_tilted
#print axioms GroundStatePosteriorFiberBridge.continuousCompatible_eq_posterior
#print axioms GroundStatePosteriorFiberBridge.normalizedFiberMeasure_ae_eq_posterior
#print axioms GroundStatePosteriorFiberBridge.fiberIntegral_ae_eq_posteriorConditionalExpectation

end MGAP4D.MathlibAnalytic
