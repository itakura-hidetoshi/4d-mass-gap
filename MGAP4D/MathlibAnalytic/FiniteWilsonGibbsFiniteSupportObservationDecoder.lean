import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsGlobalObservationLeftInverse

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Reduce global Wilson reconstruction to a finite observation support.

The global observation is assembled from singleton observations and its restriction
back to any finite support agrees with the original finite-dimensional observation.
Consequently, a left inverse for one finite observation map already supplies a left
inverse for the full global observation map.
-/

/-- A finite family of Wilson observations that reconstructs the complete source
configuration. -/
structure FiniteWilsonGibbsFiniteSupportObservationDecoder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W) where
  support : Finset EuclideanFourSpace
  reconstructFinite :
    (∀ x : support, R.fieldValue x) →
      (W.system R.sourceScale).Configuration
  reconstruct_observe :
    Function.LeftInverse reconstructFinite (R.observe support)

/-- Restriction of the global observation to the decoder support recovers the
finite observation used by the decoder. -/
theorem FiniteWilsonGibbsFiniteSupportObservationDecoder.restrict_globalObserve
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R)
    (A : (W.system R.sourceScale).Configuration) :
    D.support.restrict (R.globalObserve A) = R.observe D.support A := by
  exact finite_wilson_gibbs_single_source_globalObserve_restrict R D.support A

/-- A finite-support decoder canonically extends to a decoder of the complete
global observation. -/
noncomputable def
    FiniteWilsonGibbsFiniteSupportObservationDecoder.toGlobalObservationLeftInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsGlobalObservationLeftInverse R :=
  { reconstruct := fun φ => D.reconstructFinite (D.support.restrict φ)
    reconstruct_globalObserve := by
      intro A
      change D.reconstructFinite
        (D.support.restrict (R.globalObserve A)) = A
      calc
        D.reconstructFinite (D.support.restrict (R.globalObserve A)) =
            D.reconstructFinite (R.observe D.support A) :=
          congrArg D.reconstructFinite (D.restrict_globalObserve A)
        _ = A := D.reconstruct_observe A }

/-- Finite-support reconstruction implies faithfulness of the global observation. -/
def FiniteWilsonGibbsFiniteSupportObservationDecoder.toFaithfulGlobalObservation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsFaithfulGlobalObservation R :=
  D.toGlobalObservationLeftInverse.toFaithfulGlobalObservation

/-- Finite-support reconstruction and source nontriviality generate globally
separated Wilson configurations. -/
noncomputable def
    FiniteWilsonGibbsFiniteSupportObservationDecoder.toGlobalObservationSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsGlobalObservationSeparation R :=
  D.toGlobalObservationLeftInverse.toGlobalObservationSeparation

/-- Finite-support reconstruction generates a nondegenerate finite-cylinder event. -/
noncomputable def
    FiniteWilsonGibbsFiniteSupportObservationDecoder.toNondegenerateEvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsCylinderNondegenerateEvent R :=
  D.toGlobalObservationLeftInverse.toNondegenerateEvent

/-- Finite-support reconstruction generates the interaction witness used by the
continuum construction. -/
noncomputable def
    FiniteWilsonGibbsFiniteSupportObservationDecoder.toInteractionWitness
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsCylinderInteractionWitness R :=
  D.toGlobalObservationLeftInverse.toInteractionWitness

/-- The interaction reconstructed from finite observations survives in the
continuum connected correlation. -/
theorem finite_wilson_finite_support_decoder_interaction_passes_to_continuum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R)
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    finiteWilsonContinuumCylinderConnectedCorrelation R L
      D.toInteractionWitness.support
      D.toInteractionWitness.leftObservable
      D.toInteractionWitness.rightObservable ≠ 0 := by
  exact finite_wilson_global_observation_left_inverse_interaction_passes_to_continuum
    R L D.toGlobalObservationLeftInverse

/-- Build the exact-gap continuum assembly from a decoder on one finite support. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapContinuumAssemblyOfFiniteSupportDecoder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R :=
  C.toExactGapContinuumAssemblyOfGlobalObservationLeftInverse
    D.toGlobalObservationLeftInverse

/-- Finite-support reconstruction supplies the complete five-property Schwinger
frontier package. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteSupportDecoder_complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssemblyOfFiniteSupportDecoder D).interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssemblyOfFiniteSupportDecoder D).gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssemblyOfFiniteSupportDecoder D).schwingerFunctionsAreContinuumLimits := by
  exact C.globalObservationLeftInverse_complete_frontier_package
    D.toGlobalObservationLeftInverse

/-- Finite-support reconstruction retains the exact-threshold spectral endpoint. -/
theorem
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.finiteSupportDecoder_exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [Nontrivial (W.system R.sourceScale).Configuration]
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (D : FiniteWilsonGibbsFiniteSupportObservationDecoder R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpineOfGlobalObservationSeparation
        D.toGlobalObservationSeparation).toConstructionSpine := by
  exact C.globalObservationLeftInverse_exactThresholdSeparation
    D.toGlobalObservationLeftInverse

end

end MathlibAnalytic
end MGAP4D
