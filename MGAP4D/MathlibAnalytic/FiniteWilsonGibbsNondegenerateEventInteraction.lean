import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsConcreteAnalyticFrontierAssembly
import Mathlib.MeasureTheory.Integral.SetToL1

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Construct an interaction witness from one nondegenerate finite-cylinder event.

For an event `s` with Wilson Gibbs probability `p` strictly between zero and
one, its indicator has connected correlation with itself equal to
`p - p * p = p * (1 - p)`, hence is nonzero.  This replaces the arbitrary pair
of observables and arbitrary nonzero-correlation proof by the more geometric
input of one measurable cylinder event with nontrivial probability.
-/

/-- The real probability of a finite-cylinder event under the fixed Wilson
Gibbs marginal. -/
noncomputable def finiteWilsonGibbsCylinderEventProbability
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    (s : Set (FiniteWilsonGibbsCylinderConfiguration R J)) : ℝ :=
  ((W.system R.sourceScale).gibbsMeasure.map (R.observe J) s).toReal

/-- Real indicator observable of a finite-cylinder event. -/
def finiteWilsonGibbsCylinderEventIndicator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    (s : Set (FiniteWilsonGibbsCylinderConfiguration R J)) :
    FiniteWilsonGibbsCylinderObservable R J :=
  s.indicator (fun _ => (1 : ℝ))

/-- A measurable finite-cylinder event with probability strictly between zero
and one. -/
structure FiniteWilsonGibbsCylinderNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  support : Finset EuclideanFourSpace
  event : Set (FiniteWilsonGibbsCylinderConfiguration R support)
  event_measurable : MeasurableSet event
  probability_pos :
    0 < finiteWilsonGibbsCylinderEventProbability R support event
  probability_lt_one :
    finiteWilsonGibbsCylinderEventProbability R support event < 1

/-- The Wilson Gibbs Schwinger value of an event indicator is its event
probability. -/
theorem finite_wilson_gibbs_event_indicator_schwinger
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    (s : Set (FiniteWilsonGibbsCylinderConfiguration R J))
    (hs : MeasurableSet s) :
    finiteWilsonGibbsCylinderSchwingerValue R J
        (finiteWilsonGibbsCylinderEventIndicator R J s) =
      finiteWilsonGibbsCylinderEventProbability R J s := by
  unfold finiteWilsonGibbsCylinderSchwingerValue
    finiteWilsonGibbsCylinderEventIndicator
    finiteWilsonGibbsCylinderEventProbability
  rw [integral_indicator hs]
  simpa [measureReal_def]

/-- Squaring a real event indicator leaves it unchanged. -/
theorem finite_wilson_gibbs_event_indicator_mul_self
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    (s : Set (FiniteWilsonGibbsCylinderConfiguration R J)) :
    (fun X =>
      finiteWilsonGibbsCylinderEventIndicator R J s X *
        finiteWilsonGibbsCylinderEventIndicator R J s X) =
      finiteWilsonGibbsCylinderEventIndicator R J s := by
  funext X
  by_cases hX : X ∈ s
  · simp [finiteWilsonGibbsCylinderEventIndicator, hX]
  · simp [finiteWilsonGibbsCylinderEventIndicator, hX]

/-- The self-connected correlation of an event indicator is `p - p²`. -/
theorem finite_wilson_gibbs_event_indicator_connected
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (J : Finset EuclideanFourSpace)
    (s : Set (FiniteWilsonGibbsCylinderConfiguration R J))
    (hs : MeasurableSet s) :
    finiteWilsonGibbsCylinderConnectedCorrelation R J
        (finiteWilsonGibbsCylinderEventIndicator R J s)
        (finiteWilsonGibbsCylinderEventIndicator R J s) =
      finiteWilsonGibbsCylinderEventProbability R J s -
        finiteWilsonGibbsCylinderEventProbability R J s *
          finiteWilsonGibbsCylinderEventProbability R J s := by
  unfold finiteWilsonGibbsCylinderConnectedCorrelation
  rw [finite_wilson_gibbs_event_indicator_mul_self R J s]
  rw [finite_wilson_gibbs_event_indicator_schwinger R J s hs]

/-- A nondegenerate event has strictly positive indicator variance. -/
theorem finite_wilson_gibbs_nondegenerate_event_connected_pos
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (E : FiniteWilsonGibbsCylinderNondegenerateEvent R) :
    0 < finiteWilsonGibbsCylinderConnectedCorrelation R E.support
      (finiteWilsonGibbsCylinderEventIndicator R E.support E.event)
      (finiteWilsonGibbsCylinderEventIndicator R E.support E.event) := by
  rw [finite_wilson_gibbs_event_indicator_connected R E.support E.event
    E.event_measurable]
  let p := finiteWilsonGibbsCylinderEventProbability R E.support E.event
  have hp : 0 < p := E.probability_pos
  have hp1 : 0 < 1 - p := sub_pos.mpr E.probability_lt_one
  nlinarith [mul_pos hp hp1]

/-- Canonical interaction witness generated by one nondegenerate cylinder
event. -/
noncomputable def finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (E : FiniteWilsonGibbsCylinderNondegenerateEvent R) :
    FiniteWilsonGibbsCylinderInteractionWitness R where
  support := E.support
  leftObservable :=
    finiteWilsonGibbsCylinderEventIndicator R E.support E.event
  rightObservable :=
    finiteWilsonGibbsCylinderEventIndicator R E.support E.event
  finiteConnectedCorrelation_ne_zero :=
    ne_of_gt (finite_wilson_gibbs_nondegenerate_event_connected_pos R E)

/-- The event-generated interaction witness survives in the continuum law. -/
theorem finite_wilson_nondegenerate_event_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    (D : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (E : FiniteWilsonGibbsCylinderNondegenerateEvent R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R D E.support
      (finiteWilsonGibbsCylinderEventIndicator R E.support E.event)
      (finiteWilsonGibbsCylinderEventIndicator R E.support E.event) ≠ 0 := by
  exact finite_wilson_cylinder_interaction_passes_to_continuum R D
    (finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent R E)

/-- A nondegenerate event now supplies the complete five-property, Schwinger,
and interaction frontier package without separately supplying observables or a
connected-correlation proof. -/
theorem finite_wilson_nondegenerate_event_complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (E : FiniteWilsonGibbsCylinderNondegenerateEvent R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssembly
        (finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent R E)).interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssembly
        (finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent R E)).gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssembly
        (finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent R E)).schwingerFunctionsAreContinuumLimits := by
  exact C.complete_frontier_package
    (finiteWilsonGibbsInteractionWitnessOfNondegenerateEvent R E)

end

end MathlibAnalytic
end MGAP4D
