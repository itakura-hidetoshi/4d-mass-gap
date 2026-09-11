import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsCylinderSchwingerInteractionLimit

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
A dependency-reduced finite-Wilson continuum assembly with concrete analytic
frontier propositions.

The earlier exact-gap continuum assembly retained three arbitrary propositions:
construction of an interacting limit, construction of gauge-invariant
Schwinger functions, and identification of Schwinger functions as continuum
limits.  This file removes those proposition-valued inputs.

The replacement core retains only the exact-gap limit data and the two
reconstruction bridges.  A finite-source nonfactorization witness supplies the
interaction content.  Gauge-invariant cylinder observables and their Schwinger
functionals are constructed directly, and their exact continuum-limit identity
is theorem-generated from projective marginal recovery.

The remaining nonfactorization witness is explicit mathematical data.  This
file does not manufacture such a witness for a particular physical Wilson
coupling and does not claim an unconditional Yang--Mills construction.
-/

/-- Core data for the exact-gap continuum assembly after removing the three
opaque analytic-frontier propositions. -/
structure FiniteWilsonGibbsConcreteAnalyticFrontierCore
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)] where
  limitData : FiniteWilsonGibbsSingleSourceExactGapOSLimitData R
  measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge
  measureBridge_identified :
    measureBridge.measure =
      (R.explicitOSContinuumConstruction
        (R.automaticOSLimitTransferData limitData.toAutomaticData)).toMeasurePackage
  definitionBridge : OSWightmanExactGapDefinitionBridge
  definitionBridge_uses_measure_axioms :
    definitionBridge.spine.axioms = measureBridge.axioms

/-- Extract the proposition-free analytic core from an existing assembly.
The three old frontier propositions and their proofs are deliberately ignored. -/
def FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly.toConcreteAnalyticFrontierCore
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (A : FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R) :
    FiniteWilsonGibbsConcreteAnalyticFrontierCore R where
  limitData := A.limitData
  measureBridge := A.measureBridge
  measureBridge_identified := A.measureBridge_identified
  definitionBridge := A.definitionBridge
  definitionBridge_uses_measure_axioms := A.definitionBridge_uses_measure_axioms

/-- Build the exact-gap continuum assembly with concrete interaction and
Schwinger propositions. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapContinuumAssembly
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    FiniteWilsonGibbsSingleSourceExactGapContinuumAssembly R :=
  { limitData := C.limitData
    measureBridge := C.measureBridge
    measureBridge_identified := C.measureBridge_identified
    definitionBridge := C.definitionBridge
    definitionBridge_uses_measure_axioms :=
      C.definitionBridge_uses_measure_axioms
    interactingContinuumLimitConstructed :=
      finiteWilsonContinuumCylinderConnectedCorrelation R C.limitData I.support
        I.leftObservable I.rightObservable ≠ 0
    interactingContinuumLimitConstructed_proof :=
      finite_wilson_cylinder_interaction_passes_to_continuum
        R C.limitData I
    gaugeInvariantSchwingerFunctionsConstructed :=
      FiniteWilsonGaugeInvariantCylinderSchwingerConstructedProp R C.limitData
    gaugeInvariantSchwingerFunctionsConstructed_proof :=
      finite_wilson_gauge_invariant_cylinder_schwinger_constructed
        R C.limitData
    schwingerFunctionsAreContinuumLimits :=
      FiniteWilsonCylinderSchwingerLimitProp R C.limitData
    schwingerFunctionsAreContinuumLimits_proof :=
      finite_wilson_cylinder_schwinger_limit R C.limitData }

/-- The rebuilt assembly's interaction statement is exactly the continuum
nonfactorization statement supplied by the finite witness. -/
theorem FiniteWilsonGibbsConcreteAnalyticFrontierCore.interacting_frontier
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    (C.toExactGapContinuumAssembly I).interactingContinuumLimitConstructed := by
  exact finite_wilson_cylinder_interaction_passes_to_continuum
    R C.limitData I

/-- The rebuilt assembly contains a concrete gauge-invariant Schwinger domain. -/
theorem FiniteWilsonGibbsConcreteAnalyticFrontierCore.schwinger_constructed_frontier
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    (C.toExactGapContinuumAssembly I).gaugeInvariantSchwingerFunctionsConstructed := by
  exact finite_wilson_gauge_invariant_cylinder_schwinger_constructed
    R C.limitData

/-- The rebuilt assembly's Schwinger-limit statement is an exact theorem for all
finite-cylinder observables. -/
theorem FiniteWilsonGibbsConcreteAnalyticFrontierCore.schwinger_limit_frontier
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    (C.toExactGapContinuumAssembly I).schwingerFunctionsAreContinuumLimits := by
  exact finite_wilson_cylinder_schwinger_limit R C.limitData

/-- The rebuilt assembly simultaneously carries all five OS properties, the
concrete Schwinger construction and limit theorem, and a nonzero continuum
connected correlation. -/
theorem FiniteWilsonGibbsConcreteAnalyticFrontierCore.complete_frontier_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    FiniteWilsonExactGapOSFiveLimitProperties C.limitData ∧
      (C.toExactGapContinuumAssembly I).interactingContinuumLimitConstructed ∧
      (C.toExactGapContinuumAssembly I).gaugeInvariantSchwingerFunctionsConstructed ∧
      (C.toExactGapContinuumAssembly I).schwingerFunctionsAreContinuumLimits := by
  exact ⟨
    finite_wilson_exact_gap_os_five_limit_properties C.limitData,
    C.interacting_frontier I,
    C.schwinger_constructed_frontier I,
    C.schwinger_limit_frontier I⟩

/-- The proposition-free core and an explicit interaction witness generate the
full dependency-reduced exact-gap construction spine used by the downstream
spectral theorem packages. -/
noncomputable def
    FiniteWilsonGibbsConcreteAnalyticFrontierCore.toExactGapConstructionSpine
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpine :=
  (C.toExactGapContinuumAssembly I).toExactGapConstructionSpine

/-- The concrete frontier construction still reaches the exact-threshold
spectral separation endpoint. -/
theorem FiniteWilsonGibbsConcreteAnalyticFrontierCore.exactThresholdSeparation
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    {R : FiniteWilsonGibbsSingleSourceProjectiveRealization W}
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (C : FiniteWilsonGibbsConcreteAnalyticFrontierCore R)
    (I : FiniteWilsonGibbsCylinderInteractionWitness R) :
    euclideanYangMillsCompleteConstructionDirectBounded_exactThresholdSeparationProp
      (C.toExactGapConstructionSpine I).toConstructionSpine := by
  exact
    euclideanYangMillsContinuumMeasureExactGapConstructionSpine_exactThresholdSeparation
      (C.toExactGapConstructionSpine I)

end

end MathlibAnalytic
end MGAP4D
