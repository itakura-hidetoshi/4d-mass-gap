import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsFiniteObservationSeparation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Reduce finite Wilson observation injectivity to pointwise coordinate separation.

Instead of assuming injectivity of the complete finite observation map, it is
enough to know that every pair of distinct source configurations is separated
at one observed spacetime coordinate in a fixed finite support.  Function
extensionality then recovers injectivity of the finite observation map.
-/

/-- A finite observation support whose coordinates distinguish every pair of
finite Wilson source configurations. -/
structure FiniteWilsonGibbsFiniteCoordinateSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  support : Finset EuclideanFourSpace
  separates :
    ∀ {A B : (W.system R.sourceScale).Configuration},
      A ≠ B → ∃ x : support, R.observe support A x ≠ R.observe support B x

/-- Coordinate separation implies injectivity of the finite observation map. -/
theorem FiniteWilsonGibbsFiniteCoordinateSeparation.injective_observe
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    Function.Injective (R.observe S.support) := by
  intro A B hAB
  by_contra hne
  obtain ⟨x, hx⟩ := S.separates hne
  exact hx (congrFun hAB x)

/-- Pointwise coordinate separation supplies finite observation separation. -/
def FiniteWilsonGibbsFiniteCoordinateSeparation.toFiniteObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonGibbsFiniteObservationSeparation R where
  support := S.support
  injective_observe := S.injective_observe

/-- Coordinate separation proves faithfulness of the complete global
observation. -/
def FiniteWilsonGibbsFiniteCoordinateSeparation.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R :=
  S.toFiniteObservationSeparation.toFaithfulGlobalObservation

/-- Coordinate separation and source nontriviality generate globally separated
Wilson configurations. -/
noncomputable def
    FiniteWilsonGibbsFiniteCoordinateSeparation.toGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonGibbsGlobalObservationSeparation R :=
  S.toFiniteObservationSeparation.toGlobalObservationSeparation

/-- Coordinate separation generates a nondegenerate cylinder event. -/
noncomputable def
    FiniteWilsonGibbsFiniteCoordinateSeparation.toNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonGibbsCylinderNondegenerateEvent R :=
  S.toFiniteObservationSeparation.toNondegenerateEvent

/-- Coordinate separation generates the finite-cylinder interaction witness. -/
noncomputable def
    FiniteWilsonGibbsFiniteCoordinateSeparation.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  S.toFiniteObservationSeparation.toInteractionWitness

/-- The coordinate-separation interaction witness survives in the continuum
connected correlation. -/
theorem finite_wilson_finite_coordinate_separation_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      S.toInteractionWitness.support
      S.toInteractionWitness.leftObservable
      S.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_finite_observation_separation_interaction_passes_to_continuum
    R L S.toFiniteObservationSeparation

/-- Build the exact-gap continuum assembly from finite coordinate separation. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapContinuumAssemblyOfFiniteCoordinateSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R :=
  C.toExactGapContinuumAssemblyOfFiniteObservationSeparation
    S.toFiniteObservationSeparation

/-- Coordinate separation supplies the complete five-property Schwinger
frontier package. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteCoordinateSeparation_complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssemblyOfFiniteCoordinateSeparation S).interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssemblyOfFiniteCoordinateSeparation S).gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssemblyOfFiniteCoordinateSeparation S).schwingerFunctionsAreContinuumLimits := by
  exact C.finiteObservationSeparation_complete_frontier_package
    S.toFiniteObservationSeparation

/-- Coordinate separation retains the exact-threshold spectral endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteCoordinateSeparation_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (S : FiniteWilsonGibbsFiniteCoordinateSeparation R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        S.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.finiteObservationSeparation_exactThresholdSeparation
    S.toFiniteObservationSeparation

end

end MathlibAnalytic
end MGAP4D
