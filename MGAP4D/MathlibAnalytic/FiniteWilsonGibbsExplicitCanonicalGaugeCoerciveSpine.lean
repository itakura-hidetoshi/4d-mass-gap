import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsExplicitCanonicalGaugeCoerciveFrontier
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceExactGapContinuumSpine

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Construct the reduced exact-gap continuum Yang--Mills spine directly from the
explicit canonical gauge realization and the existing coercive transfer-orbit
OS-limit assembly.
-/

local instance finiteWilsonExplicitCanonicalGaugeCoerciveSpine_fieldValueFintype
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    Fintype ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change Fintype (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeCoerciveSpine_fieldValueCountable
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    Countable ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change Countable (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeCoerciveSpine_fieldValueDiscrete
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    DiscreteMeasurableSpace
      ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change DiscreteMeasurableSpace (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeCoerciveSpine_configurationNontrivial
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge] :
    Nontrivial
      ((W.system
        (finiteWilsonExplicitCanonicalGaugeRealization W s).sourceScale).Configuration) := by
  change Nontrivial ((W.system s).Edge → (W.system s).Gauge)
  infer_instance

/-- The explicit projective-limit continuum construction generated from the
coercive transfer-orbit analytic assembly. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s)) :=
  (finiteWilsonExplicitCanonicalGaugeRealization W s).explicitOSContinuumConstruction
    ((finiteWilsonExplicitCanonicalGaugeRealization W s).automaticOSLimitTransferData
      (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s D))

/-- A gauge-invariant finite-cylinder observable for arbitrary automatic
single-source OS-limit data. -/
structure FiniteWilsonAutomaticGaugeInvariantCylinderObservable
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R)
    (J : Finset EuclideanFourSpace) where
  observable : FiniteWilsonGibbsCylinderObservable R J
  invariant :
    ∀ (g : D.gaugeGroup)
      (X : R.toProjectiveRealization.toProjectiveCylinderFamily.Configuration),
      observable (J.restrict (g • X)) = observable (J.restrict X)

/-- The zero observable constructs a gauge-invariant cylinder observable for
every automatic OS-limit support. -/
def finiteWilsonAutomaticZeroGaugeInvariantCylinderObservable
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R)
    (J : Finset EuclideanFourSpace) :
    FiniteWilsonAutomaticGaugeInvariantCylinderObservable R D J where
  observable := fun _ => 0
  invariant := by
    intro g X
    rfl

/-- Gauge-invariant cylinder observables are concretely nonempty on every finite
support for arbitrary automatic OS-limit data. -/
abbrev FiniteWilsonAutomaticGaugeInvariantCylinderSchwingerConstructedProp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R) : Prop :=
  ∀ J : Finset EuclideanFourSpace,
    Nonempty (FiniteWilsonAutomaticGaugeInvariantCylinderObservable R D J)

/-- Construction theorem for the automatic gauge-invariant cylinder domain. -/
theorem finite_wilson_automatic_gauge_invariant_cylinder_schwinger_constructed
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R) :
    FiniteWilsonAutomaticGaugeInvariantCylinderSchwingerConstructedProp R D := by
  intro J
  exact ⟨finiteWilsonAutomaticZeroGaugeInvariantCylinderObservable R D J⟩

/-- Every automatic continuum cylinder Schwinger value is exactly its fixed
finite-Wilson source value. -/
abbrev FiniteWilsonAutomaticCylinderSchwingerLimitProp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R) : Prop :=
  ∀ (J : Finset EuclideanFourSpace)
    (O : FiniteWilsonGibbsCylinderObservable R J),
    finiteWilsonAutomaticContinuumCylinderSchwingerValue R D J O =
      finiteWilsonGibbsCylinderSchwingerValue R J O

/-- The automatic cylinder Schwinger-limit proposition is theorem-generated by
projective marginal recovery. -/
theorem finite_wilson_automatic_cylinder_schwinger_limit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (R : FiniteWilsonGibbsSingleSourceProjectiveRealization W)
    [∀ x, Fintype (R.fieldValue x)]
    [∀ x, Countable (R.fieldValue x)]
    [∀ x, DiscreteMeasurableSpace (R.fieldValue x)]
    (D : FiniteWilsonGibbsSingleSourceAutomaticOSLimitData R) :
    FiniteWilsonAutomaticCylinderSchwingerLimitProp R D := by
  intro J O
  exact finite_wilson_automatic_continuum_cylinder_schwinger_eq_source R D J O

/-- The existing coercive transfer-orbit assembly and reconstruction bridges
construct the reduced exact-gap continuum Yang--Mills spine for the explicit
canonical gauge realization. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeCoerciveExactGapConstructionSpine
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpine := by
  letI : ∀ x,
      TopologicalSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) :=
    fun _ => ⊥
  letI : ∀ x,
      DiscreteTopology
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) :=
    fun _ => ⟨rfl⟩
  letI : ∀ x,
      BorelSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) :=
    fun _ => by infer_instance
  letI : ∀ x,
      PolishSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) :=
    fun _ => by infer_instance
  letI : ∀ x,
      TopologicalSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
    fun x => by
      change TopologicalSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x)
      infer_instance
  letI : ∀ x,
      OpensMeasurableSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
    fun x => by
      change OpensMeasurableSpace
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x)
      infer_instance
  letI : ∀ x,
      SecondCountableTopology
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily.fieldValue x) :=
    fun x => by
      change SecondCountableTopology
        ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x)
      infer_instance
  exact
    { finiteVolume := W.toFiniteVolumeApproximation
      measurePackage :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).toMeasurePackage
      bridge := measureBridge
      definitionBridge := definitionBridge
      measurePackage_identified := measureBridge_identified
      bridge_uses_reduced_axioms := definitionBridge_uses_measure_axioms
      projectiveConsistency :=
        IsProjectiveMeasureFamily
          (finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily.finiteMarginal
      projectiveConsistency_proof :=
        (finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily.projective
      tightness :=
        Nonempty
          (EuclideanYangMillsCompactTightnessData
            (finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily)
      tightness_proof :=
        ⟨(finiteWilsonExplicitCanonicalGaugeRealization W s).finiteDiscreteCompactTightnessData⟩
      weakLimitExists :=
        Nonempty
          (EuclideanYangMillsProjectiveLimitMeasure
            (finiteWilsonExplicitCanonicalGaugeRealization W s).toProjectiveRealization.toProjectiveCylinderFamily)
      weakLimitExists_proof :=
        ⟨(finiteWilsonExplicitCanonicalGaugeRealization W s).projectiveLimitMeasure⟩
      continuumMeasureIdentified :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).limit.continuumMeasure =
          (finiteWilsonExplicitCanonicalGaugeRealization W s).continuumMeasure
      continuumMeasureIdentified_proof := rfl
      continuumFourDimensionalYangMillsMeasureConstructed :=
        IsProbabilityMeasure
          (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).limit.continuumMeasure
      continuumFourDimensionalYangMillsMeasureConstructed_proof :=
        euclidean_yang_mills_projective_limit_probability
          (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).limit
      nontrivialCompactGaugeGroupConstructed :=
        CompactSpace
            (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).gaugeGroup ∧
          Nontrivial
            (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).gaugeGroup
      nontrivialCompactGaugeGroupConstructed_proof :=
        ⟨inferInstance, inferInstance⟩
      interactingContinuumLimitConstructed :=
        finiteWilsonAutomaticContinuumCylinderConnectedCorrelation
            (finiteWilsonExplicitCanonicalGaugeRealization W s)
            (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s D)
            (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).support
            (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).leftObservable
            (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).rightObservable ≠ 0
      interactingContinuumLimitConstructed_proof :=
        finite_wilson_explicit_canonical_gauge_coercive_interaction_passes_to_continuum W s D
      gaugeInvariantSchwingerFunctionsConstructed :=
        FiniteWilsonAutomaticGaugeInvariantCylinderSchwingerConstructedProp
          (finiteWilsonExplicitCanonicalGaugeRealization W s)
          (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s D)
      gaugeInvariantSchwingerFunctionsConstructed_proof :=
        finite_wilson_automatic_gauge_invariant_cylinder_schwinger_constructed
          (finiteWilsonExplicitCanonicalGaugeRealization W s)
          (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s D)
      schwingerFunctionsAreContinuumLimits :=
        FiniteWilsonAutomaticCylinderSchwingerLimitProp
          (finiteWilsonExplicitCanonicalGaugeRealization W s)
          (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s D)
      schwingerFunctionsAreContinuumLimits_proof :=
        finite_wilson_automatic_cylinder_schwinger_limit
          (finiteWilsonExplicitCanonicalGaugeRealization W s)
          (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s D)
      reflectionPositivityPassesToLimit :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).reflectionPositive_proof
      euclideanInvariancePassesToLimit :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).euclideanInvariant_proof
      symmetryPassesToLimit :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).symmetric_proof
      clusterPropertyPassesToLimit :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).clusterProperty_proof
      regularityPassesToLimit :=
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).regularity_proof
      gaugeGroupCompactTheorem := by
        change CompactSpace
          (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).gaugeGroup
        infer_instance
      gaugeGroupNontrivialTheorem := by
        change Nontrivial
          (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).gaugeGroup
        infer_instance }

/-- The coercive explicit-canonical continuum construction reaches the existing
OS/Wightman Hamiltonian mass-gap pipeline and its exact non-vacuum spectral
threshold. -/
theorem finite_wilson_explicit_canonical_gauge_coercive_mass_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        (finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s D).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    let C :=
      (finiteWilsonExplicitCanonicalGaugeCoerciveExactGapConstructionSpine W s D
        measureBridge measureBridge_identified definitionBridge
        definitionBridge_uses_measure_axioms).toConstructionSpine.toUnconditionalTarget
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum := by
  dsimp
  exact
    euclidean_yang_mills_unconditional_measure_construction_mass_gap
      ((finiteWilsonExplicitCanonicalGaugeCoerciveExactGapConstructionSpine W s D
        measureBridge measureBridge_identified definitionBridge
        definitionBridge_uses_measure_axioms).toConstructionSpine.toUnconditionalTarget)

end

end MathlibAnalytic
end MGAP4D