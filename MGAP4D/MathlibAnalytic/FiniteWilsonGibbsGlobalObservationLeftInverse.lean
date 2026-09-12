import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsFaithfulGlobalObservationSeparation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Generate global-observation faithfulness from an explicit reconstruction map.

The previous frontier retains injectivity of `R.globalObserve` as its remaining
observation obligation.  A left inverse is stronger and more constructive: a
continuum observation can be decoded back to the original finite Wilson source
configuration.  This file proves injectivity from that reconstruction identity
and propagates it through the nondegenerate-event, interaction, Schwinger, and
exact-threshold frontier.
-/

/-- A decoder recovering every finite Wilson source configuration from its full
global observation. -/
structure FiniteWilsonGibbsGlobalObservationLeftInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  reconstruct :
    R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration →
      (W.system R.sourceScale).Configuration
  reconstruct_globalObserve :
    Function.LeftInverse reconstruct R.globalObserve

/-- A reconstruction map proves that the global observation is faithful. -/
def FiniteWilsonGibbsGlobalObservationLeftInverse.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R where
  injective_globalObserve := by
    intro A B hAB
    calc
      A = L.reconstruct (R.globalObserve A) :=
        (L.reconstruct_globalObserve A).symm
      _ = L.reconstruct (R.globalObserve B) := congrArg L.reconstruct hAB
      _ = B := L.reconstruct_globalObserve B

/-- Reconstruction and source nontriviality generate two globally separated
finite Wilson configurations. -/
noncomputable def
    FiniteWilsonGibbsGlobalObservationLeftInverse.toGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    FiniteWilsonGibbsGlobalObservationSeparation R :=
  L.toFaithfulGlobalObservation.toGlobalObservationSeparation

/-- Reconstruction generates a nondegenerate singleton cylinder event. -/
noncomputable def
    FiniteWilsonGibbsGlobalObservationLeftInverse.toNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    FiniteWilsonGibbsCylinderNondegenerateEvent R :=
  L.toFaithfulGlobalObservation.toNondegenerateEvent

/-- Reconstruction generates the finite-cylinder interaction witness. -/
noncomputable def
    FiniteWilsonGibbsGlobalObservationLeftInverse.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  L.toFaithfulGlobalObservation.toInteractionWitness

/-- The reconstruction-generated interaction survives in the continuum law. -/
theorem finite_wilson_global_observation_left_inverse_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R D
      L.toInteractionWitness.support
      L.toInteractionWitness.leftObservable
      L.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_faithful_global_observation_interaction_passes_to_continuum
    R D L.toFaithfulGlobalObservation

/-- Build the exact-gap continuum assembly from a global-observation decoder. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapContinuumAssemblyOfGlobalObservationLeftInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R :=
  C.toExactGapContinuumAssemblyOfFaithfulGlobalObservation
    L.toFaithfulGlobalObservation

/-- A decoder supplies the five OS properties, concrete Schwinger construction
and limit, and continuum interaction theorem in one package. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservationLeftInverse_complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssemblyOfGlobalObservationLeftInverse L).interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssemblyOfGlobalObservationLeftInverse L).gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssemblyOfGlobalObservationLeftInverse L).schwingerFunctionsAreContinuumLimits := by
  exact C.faithfulGlobalObservation_complete_frontier_package
    L.toFaithfulGlobalObservation

/-- The reconstruction route retains exact-threshold spectral separation. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.globalObservationLeftInverse_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (L : FiniteWilsonGibbsGlobalObservationLeftInverse R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        L.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.globalObservation_exactThresholdSeparation
    L.toGlobalObservationSeparation

end

end MathlibAnalytic
end MGAP4D
