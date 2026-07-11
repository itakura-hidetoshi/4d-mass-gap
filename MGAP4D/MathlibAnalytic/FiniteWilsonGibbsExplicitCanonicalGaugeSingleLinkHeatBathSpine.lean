import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsExplicitCanonicalGaugeCoerciveSpine
import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitAssembly

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Connect the explicit canonical gauge realization directly to the concrete
single-link Wilson heat-bath Poincare assembly.
-/

local instance finiteWilsonExplicitCanonicalGaugeHeatBath_fieldValueFintype
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    Fintype ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change Fintype (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeHeatBath_fieldValueCountable
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    Countable ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change Countable (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeHeatBath_fieldValueDiscrete
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (x : EuclideanFourSpace) :
    DiscreteMeasurableSpace
      ((finiteWilsonExplicitCanonicalGaugeRealization W s).fieldValue x) := by
  change DiscreteMeasurableSpace (W.system s).Gauge
  infer_instance

local instance finiteWilsonExplicitCanonicalGaugeHeatBath_configurationNontrivial
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge] :
    Nontrivial
      ((W.system
        (finiteWilsonExplicitCanonicalGaugeRealization W s).sourceScale).Configuration) := by
  change Nontrivial ((W.system s).Edge → (W.system s).Gauge)
  infer_instance

/-- The single-link heat-bath Poincare assembly generates exactly the coercive
transfer-orbit datum consumed by the explicit canonical continuum spine. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathCoerciveData
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s)) :
    FiniteWilsonGibbsSingleSourceCoerciveTransferOrbitOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s) :=
  D.toVacuumPoincareAnalyticData
    |>.toVacuumOrthogonalDerivedInvarianceAnalyticData
    |>.toCoerciveTransferOrbitAnalyticData

/-- The explicit canonical continuum construction generated from the concrete
single-link heat-bath route. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s)) :=
  finiteWilsonExplicitCanonicalGaugeCoerciveContinuumConstruction W s
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathCoerciveData W s D)

/-- The single-link heat-bath construction produces a nonzero continuum
connected correlation for the explicit canonical gauge observation. -/
theorem finite_wilson_explicit_canonical_gauge_singleLinkHeatBath_interaction_passes_to_continuum
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s)) :
    finiteWilsonAutomaticContinuumCylinderConnectedCorrelation
        (finiteWilsonExplicitCanonicalGaugeRealization W s)
        (finiteWilsonExplicitCanonicalGaugeCoerciveAutomaticOSLimitData W s
          (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathCoerciveData W s D))
        (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).support
        (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).leftObservable
        (finiteWilsonExplicitCanonicalGaugeInteractionWitness W s).rightObservable ≠ 0 := by
  exact finite_wilson_explicit_canonical_gauge_coercive_interaction_passes_to_continuum
    W s (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathCoerciveData W s D)

/-- The concrete single-link heat-bath Poincare route constructs the reduced
exact-gap continuum spine for the explicit canonical gauge realization. -/
noncomputable def finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathExactGapConstructionSpine
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
          W s D).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpine :=
  finiteWilsonExplicitCanonicalGaugeCoerciveExactGapConstructionSpine W s
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathCoerciveData W s D)
    measureBridge measureBridge_identified definitionBridge
    definitionBridge_uses_measure_axioms

/-- The explicit canonical single-link heat-bath construction reaches the
Hamiltonian mass-gap theorem and exact non-vacuum spectral threshold. -/
theorem finite_wilson_explicit_canonical_gauge_singleLinkHeatBath_mass_gap
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (measureBridge : EuclideanYangMillsMeasureToOSWightmanBridge)
    (measureBridge_identified :
      measureBridge.measure =
        (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
          W s D).toMeasurePackage)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms = measureBridge.axioms) :
    let C :=
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathExactGapConstructionSpine
        W s D measureBridge measureBridge_identified definitionBridge
        definitionBridge_uses_measure_axioms).toConstructionSpine.toUnconditionalTarget
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact finite_wilson_explicit_canonical_gauge_coercive_mass_gap W s
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathCoerciveData W s D)
    measureBridge measureBridge_identified definitionBridge
    definitionBridge_uses_measure_axioms

end

end MathlibAnalytic
end MGAP4D