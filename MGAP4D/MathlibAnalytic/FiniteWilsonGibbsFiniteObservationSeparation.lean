import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsFiniteSupportObservationDecoder

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Reduce global Wilson faithfulness to injectivity of one finite observation map.

A finite-support decoder is sufficient but stronger than necessary.  For the
interaction frontier it is enough that one finite family of observations
separates source configurations.  Restricting equal global observations to
that support then proves equality of the finite observations, and finite
injectivity recovers equality of the source configurations.
-/

/-- A finite spacetime support whose observation map separates all finite
Wilson source configurations. -/
structure FiniteWilsonGibbsFiniteObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  support : Finset EuclideanFourSpace
  injective_observe : Function.Injective (R.observe support)

/-- Equality of global observations implies equality after restriction to the
chosen finite separating support. -/
theorem FiniteWilsonGibbsFiniteObservationSeparation.observe_eq_of_globalObserve_eq
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteObservationSeparation R)
    {A B : (W.system R.sourceScale).Configuration}
    (hAB : R.globalObserve A = R.globalObserve B) :
    R.observe S.support A = R.observe S.support B := by
  calc
    R.observe S.support A = S.support.restrict (R.globalObserve A) :=
      (finite_wilson_gibbs_single_source_globalObserve_restrict
        R S.support A).symm
    _ = S.support.restrict (R.globalObserve B) :=
      congrArg S.support.restrict hAB
    _ = R.observe S.support B :=
      finite_wilson_gibbs_single_source_globalObserve_restrict
        R S.support B

/-- A finite separating observation family proves faithfulness of the complete
global observation. -/
def FiniteWilsonGibbsFiniteObservationSeparation.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R where
  injective_globalObserve := by
    intro A B hAB
    exact S.injective_observe (S.observe_eq_of_globalObserve_eq hAB)

/-- A finite-support decoder supplies finite observation separation. -/
def FiniteWilsonGibbsFiniteSupportObservationDecoder.toFiniteObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsFiniteObservationSeparation R where
  support := D.support
  injective_observe := by
    intro A B hAB
    calc
      A = D.reconstructFinite (R.observe D.support A) :=
        (D.reconstruct_observe A).symm
      _ = D.reconstructFinite (R.observe D.support B) :=
        congrArg D.reconstructFinite hAB
      _ = B := D.reconstruct_observe B

/-- Finite observation separation and source nontriviality generate globally
separated Wilson configurations. -/
noncomputable def
    FiniteWilsonGibbsFiniteObservationSeparation.toGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    FiniteWilsonGibbsGlobalObservationSeparation R :=
  S.toFaithfulGlobalObservation.toGlobalObservationSeparation

/-- Finite observation separation generates a nondegenerate cylinder event. -/
noncomputable def
    FiniteWilsonGibbsFiniteObservationSeparation.toNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    FiniteWilsonGibbsCylinderNondegenerateEvent R :=
  S.toFaithfulGlobalObservation.toNondegenerateEvent

/-- Finite observation separation generates the finite interaction witness. -/
noncomputable def
    FiniteWilsonGibbsFiniteObservationSeparation.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  S.toFaithfulGlobalObservation.toInteractionWitness

/-- The finite-separation interaction witness survives in the continuum law. -/
theorem finite_wilson_finite_observation_separation_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      S.toInteractionWitness.support
      S.toInteractionWitness.leftObservable
      S.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_faithful_global_observation_interaction_passes_to_continuum
    R L S.toFaithfulGlobalObservation

/-- Build the exact-gap continuum assembly from finite observation separation. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapContinuumAssemblyOfFiniteObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R :=
  C.toExactGapContinuumAssemblyOfFaithfulGlobalObservation
    S.toFaithfulGlobalObservation

/-- Finite observation separation supplies the complete five-property Schwinger
frontier package. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteObservationSeparation_complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssemblyOfFiniteObservationSeparation S).interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssemblyOfFiniteObservationSeparation S).gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssemblyOfFiniteObservationSeparation S).schwingerFunctionsAreContinuumLimits := by
  exact C.faithfulGlobalObservation_complete_frontier_package
    S.toFaithfulGlobalObservation

/-- Finite observation separation retains the exact-threshold spectral endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteObservationSeparation_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteObservationSeparation R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        S.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.globalObservation_exactThresholdSeparation
    S.toGlobalObservationSeparation

end

end MathlibAnalytic
end MGAP4D
