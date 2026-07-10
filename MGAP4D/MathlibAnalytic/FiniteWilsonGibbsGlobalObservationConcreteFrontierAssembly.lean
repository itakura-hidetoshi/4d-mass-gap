import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsGlobalObservationNondegenerateEvent
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsConcreteAnalyticFrontierAssembly

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
The concrete exact-gap continuum frontier generated from global observation
nontriviality.

The finite-cylinder event, its strict probability bounds, the indicator
observable, positive connected correlation, and the interaction witness are all
generated from two source configurations distinguished by the global
observation.
-/

/-- Build the exact-gap continuum assembly directly from global observation
separation. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapContinuumAssemblyOfGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R :=
  C.toExactGapContinuumAssembly G.toInteractionWitness

/-- The interaction field of the generated assembly is theorem-filled by the
global-observation nondegenerate event. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservation_interacting_frontier
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    (C.toExactGapContinuumAssemblyOfGlobalObservationSeparation G).
      interactingContinuumLimitConstructed := by
  exact C.interacting_frontier G.toInteractionWitness

/-- Gauge-invariant cylinder Schwinger observables are constructed in the
assembly generated from global observation separation. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservation_schwinger_constructed_frontier
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    (C.toExactGapContinuumAssemblyOfGlobalObservationSeparation G).
      gaugeInvariantSchwingerFunctionsConstructed := by
  exact C.schwinger_constructed_frontier G.toInteractionWitness

/-- The exact finite-cylinder Schwinger source identity is carried by the
assembly generated from global observation separation. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservation_schwinger_limit_frontier
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    (C.toExactGapContinuumAssemblyOfGlobalObservationSeparation G).
      schwingerFunctionsAreContinuumLimits := by
  exact C.schwinger_limit_frontier G.toInteractionWitness

/-- Global observation separation generates the five OS properties, concrete
Schwinger construction and limit, and continuum interaction theorem in one
package. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservation_complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssemblyOfGlobalObservationSeparation G).
        interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssemblyOfGlobalObservationSeparation G).
        gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssemblyOfGlobalObservationSeparation G).
        schwingerFunctionsAreContinuumLimits := by
  exact finite_wilson_nondegenerate_event_complete_frontier_package
    C G.toNondegenerateEvent

/-- Global observation separation generates the reduced exact-gap continuum
construction spine. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapConstructionSpineOfGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpine :=
  C.toExactGapConstructionSpine G.toInteractionWitness

/-- The global-observation route retains the exact-threshold spectral separation
endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservation_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (G : FiniteWilsonGibbsGlobalObservationSeparation R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation G).
        toConstructionSpine := by
  exact C.exactThresholdSeparation G.toInteractionWitness

end

end MathlibAnalytic
end MGAP4D
