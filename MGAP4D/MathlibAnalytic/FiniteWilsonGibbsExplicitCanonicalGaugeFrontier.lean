import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsExplicitCanonicalGaugeInteraction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Connect the explicit canonical gauge realization directly to the existing
exact-gap continuum assembly and concrete analytic frontier core.
-/

local instance finiteWilsonExplicitCanonicalGaugeFrontier_fieldValueFintype
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    Fintype ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change Fintype (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeFrontier_fieldValueCountable
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    Countable ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change Countable (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeFrontier_fieldValueDiscrete
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    DiscreteMeasurableSpace
      ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change DiscreteMeasurableSpace (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeFrontier_configurationNontrivial
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge] :
    Nontrivial
      ((W.system
        (finiteWilsonExplicitCanonicalGaugeRealization W s).sourceScale).Configuration) := by
  change Nontrivial ((W.system s).Edge → (W.system s).Gauge)
  infer_instance

/-- Existing exact-gap limit and reconstruction bridges generate the complete
continuum assembly for the explicit canonical gauge realization.  The
interaction and Schwinger frontier fields are filled by the explicit witness
and the finite-cylinder theorems rather than retained as proposition inputs. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeExactGapContinuumAssembly
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).explicitOSContinuumConstruction
          ((finiteWilsonExplicitCanonicalGaugeRealization W s).automaticOSLimitTransferData
            L.toAutomaticData)).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly
      (finiteWilsonExplicitCanonicalGaugeRealization W s) where
  limitData := L
  measureBridge := measureBridge
  measureBridge_identified := measureBridge_identified
  definitionBridge := definitionBridge
  definitionBridge_uses_measure_axioms := definitionBridge_uses_measure_axioms
  interactingContinuumLimitConstructed :=
    finiteWilsonContinuumCylinderConnectedCorrelation
        (finiteWilsonExplicitCanonicalGaugeRealization W s) L
        (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).support
        (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).leftObservable
        (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).rightObservable ≠ 0
  interactingContinuumLimitConstructed_proof :=
    finite_wilson_explicit_canonical_gauge_interaction_passes_to_continuum W s L
  gaugeInvariantSchwingerFunctionsConstructed :=
    FiniteWilsonGaugeInvariantCylinderSchwingerConstructedProp
      (finiteWilsonExplicitCanonicalGaugeRealization W s) L
  gaugeInvariantSchwingerFunctionsConstructed_proof :=
    finite_wilson_gauge_invariant_cylinder_schwinger_constructed
      (finiteWilsonExplicitCanonicalGaugeRealization W s) L
  schwingerFunctionsAreContinuumLimits :=
    FiniteWilsonCylinderSchwingerLimitProp
      (finiteWilsonExplicitCanonicalGaugeRealization W s) L
  schwingerFunctionsAreContinuumLimits_proof :=
    finite_wilson_cylinder_schwinger_limit
      (finiteWilsonExplicitCanonicalGaugeRealization W s) L

/-- The existing assembly-to-core constructor specializes to the explicit
canonical gauge realization. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeFrontierCore
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).explicitOSContinuumConstruction
          ((finiteWilsonExplicitCanonicalGaugeRealization W s).automaticOSLimitTransferData
            L.toAutomaticData)).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    FiniteWilsonGibbsConcreteAnalyticFrontierCore
      (finiteWilsonExplicitCanonicalGaugeRealization W s) :=
  (finiteWilsonExplicitCanonicalGaugeExactGapContinuumAssembly W s L
    measureBridge measureBridge_identified definitionBridge
    definitionBridge_uses_measure_axioms).toConcreteAnalyticFrontierCore

/-- The constructed explicit canonical frontier core reaches the exact-threshold
spectral separation endpoint. -/
theorem finite_wilson_explicit_canonical_gauge_frontier_exactThresholdSeparation
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (L : FiniteWilsonGibbsSingleSourceExactGapOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).explicitOSContinuumConstruction
          ((finiteWilsonExplicitCanonicalGaugeRealization W s).automaticOSLimitTransferData
            L.toAutomaticData)).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      ((finiteWilsonExplicitCanonicalGaugeFrontierCore W s L measureBridge
          measureBridge_identified definitionBridge
          definitionBridge_uses_measure_axioms).toExactGapConstructionSpineOfGlobalObservationSeparation
        (FiniteWilsonGibbsFiniteCoordinateSelector.toGlobalObservationSeparation
          (finiteWilsonExplicitCanonicalGaugeEdgeObservation W s).toExactLinkObservation.toFiniteCoordinateSelector)).toConstructionSpine := by
  exact
    (finiteWilsonExplicitCanonicalGaugeFrontierCore W s L measureBridge
      measureBridge_identified definitionBridge
      definitionBridge_uses_measure_axioms).explicitCanonicalGauge_exactThresholdSeparation W s

end

end MathlibAnalytic
end MGAP4D
