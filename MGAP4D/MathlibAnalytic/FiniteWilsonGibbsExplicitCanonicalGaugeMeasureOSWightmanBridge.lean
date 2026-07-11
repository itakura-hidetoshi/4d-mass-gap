import MGAP4D.MathlibAnalytic.FiniteWilsonGibbsExplicitCanonicalGaugeSingleLinkHeatBathSpine

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Construct the existing Euclidean-measure-to-OS/Wightman bridge directly from a
continuum measure package and the three genuine Wightman reconstruction maps.

The Euclidean carrier identifications and the seven measure-side OS properties
are canonical.  They are no longer repeated as an externally assembled bridge.
-/

/-- Canonical measure-to-OS/Wightman bridge.

The Euclidean and OS fields are inherited definitionally from the displayed
measure package.  Only locality, covariance, and the spectrum condition remain
as actual reconstruction theorems from measure readiness. -/
def euclideanYangMillsMeasureCanonicalOSWightmanBridge
    (μ : EuclideanYangMillsMeasurePackage)
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure : μ.ready → wightmanLocality)
    (wightmanCovariance_from_measure : μ.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      μ.ready → wightmanSpectrumCondition) :
    EuclideanYangMillsMeasureToOSWightmanBridge where
  measure := μ
  axioms :=
    { gaugeGroup := μ.gaugeGroup
      gaugeGroupCompact := μ.gaugeGroupCompact
      gaugeGroupNontrivial := μ.gaugeGroupNontrivial
      fieldAlgebra := μ.fieldAlgebra
      euclideanFieldConfigurations := μ.configurationSpace
      schwingerFunctions := μ.schwingerFunctions
      osReflectionPositive := μ.reflectionPositive
      osEuclideanInvariant := μ.euclideanInvariant
      osSymmetric := μ.symmetric
      osClusterProperty := μ.clusterProperty
      osRegularity := μ.regularity
      wightmanLocality := wightmanLocality
      wightmanCovariance := wightmanCovariance
      wightmanSpectrumCondition := wightmanSpectrumCondition }
  gaugeGroup_identified := rfl
  fieldAlgebra_identified := rfl
  euclideanConfigurationSpace_identified := rfl
  schwingerFunctions_identified := rfl
  gaugeGroupCompact_from_measure := fun h => h
  gaugeGroupNontrivial_from_measure := fun h => h
  osReflectionPositive_from_measure := fun h => h
  osEuclideanInvariant_from_measure := fun h => h
  osSymmetric_from_measure := fun h => h
  osClusterProperty_from_measure := fun h => h
  osRegularity_from_measure := fun h => h
  wightmanLocality_from_os_reconstruction := wightmanLocality_from_measure
  wightmanCovariance_from_os_reconstruction := wightmanCovariance_from_measure
  wightmanSpectrumCondition_from_os_reconstruction :=
    wightmanSpectrumCondition_from_measure

@[simp]
theorem euclideanYangMillsMeasureCanonicalOSWightmanBridge_measure
    (μ : EuclideanYangMillsMeasurePackage)
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure : μ.ready → wightmanLocality)
    (wightmanCovariance_from_measure : μ.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      μ.ready → wightmanSpectrumCondition) :
    (euclideanYangMillsMeasureCanonicalOSWightmanBridge μ
      wightmanLocality wightmanCovariance wightmanSpectrumCondition
      wightmanLocality_from_measure wightmanCovariance_from_measure
      wightmanSpectrumCondition_from_measure).measure = μ :=
  rfl

/-- The canonical bridge has a ready OS/Wightman axiom package whenever the
measure package is ready. -/
theorem euclideanYangMillsMeasureCanonicalOSWightmanBridge_ready
    (μ : EuclideanYangMillsMeasurePackage)
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure : μ.ready → wightmanLocality)
    (wightmanCovariance_from_measure : μ.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      μ.ready → wightmanSpectrumCondition)
    (hμ : μ.ready) :
    (euclideanYangMillsMeasureCanonicalOSWightmanBridge μ
      wightmanLocality wightmanCovariance wightmanSpectrumCondition
      wightmanLocality_from_measure wightmanCovariance_from_measure
      wightmanSpectrumCondition_from_measure).axioms.ready :=
  euclidean_yang_mills_measure_to_os_wightman_ready
    (euclideanYangMillsMeasureCanonicalOSWightmanBridge μ
      wightmanLocality wightmanCovariance wightmanSpectrumCondition
      wightmanLocality_from_measure wightmanCovariance_from_measure
      wightmanSpectrumCondition_from_measure)
    hμ

/-- The single-link heat-bath continuum measure package with its Euclidean
fields identified definitionally. -/
noncomputable def
    finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanLocality)
    (wightmanCovariance_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanSpectrumCondition) :
    EuclideanYangMillsMeasureToOSWightmanBridge :=
  euclideanYangMillsMeasureCanonicalOSWightmanBridge
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
      W s D).toMeasurePackage
    wightmanLocality wightmanCovariance wightmanSpectrumCondition
    wightmanLocality_from_measure wightmanCovariance_from_measure
    wightmanSpectrumCondition_from_measure

@[simp]
theorem finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge_measure
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanLocality)
    (wightmanCovariance_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanSpectrumCondition) :
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge W s D
      wightmanLocality wightmanCovariance wightmanSpectrumCondition
      wightmanLocality_from_measure wightmanCovariance_from_measure
      wightmanSpectrumCondition_from_measure).measure =
        (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
          W s D).toMeasurePackage :=
  rfl

/-- Build the reduced exact-gap construction spine without an externally
assembled measure bridge or a separate measure-package identification proof. -/
noncomputable def
    finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathExactGapConstructionSpineOfReconstruction
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanLocality)
    (wightmanCovariance_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanSpectrumCondition)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms =
        (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge W s D
          wightmanLocality wightmanCovariance wightmanSpectrumCondition
          wightmanLocality_from_measure wightmanCovariance_from_measure
          wightmanSpectrumCondition_from_measure).axioms) :
    EuclideanYangMillsContinuumMeasureExactGapConstructionSpine :=
  finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathExactGapConstructionSpine
    W s D
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge W s D
      wightmanLocality wightmanCovariance wightmanSpectrumCondition
      wightmanLocality_from_measure wightmanCovariance_from_measure
      wightmanSpectrumCondition_from_measure)
    rfl definitionBridge definitionBridge_uses_measure_axioms

/-- The single-link heat-bath route reaches the Hamiltonian mass-gap endpoint
with the measure bridge constructed canonically from reconstruction theorems. -/
theorem
    finite_wilson_explicit_canonical_gauge_singleLinkHeatBath_mass_gap_of_reconstruction
    (W : FiniteWilsonOSAutomaticApproximationFamily)
    (s : W.index)
    [Nonempty (W.system s).Edge]
    (D : FiniteWilsonGibbsSingleSourceSingleLinkHeatBathOSLimitData
      (finiteWilsonExplicitCanonicalGaugeRealization W s))
    (wightmanLocality wightmanCovariance wightmanSpectrumCondition : Prop)
    (wightmanLocality_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanLocality)
    (wightmanCovariance_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanCovariance)
    (wightmanSpectrumCondition_from_measure :
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathContinuumConstruction
        W s D).toMeasurePackage.ready → wightmanSpectrumCondition)
    (definitionBridge : OSWightmanExactGapDefinitionBridge)
    (definitionBridge_uses_measure_axioms :
      definitionBridge.spine.axioms =
        (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge W s D
          wightmanLocality wightmanCovariance wightmanSpectrumCondition
          wightmanLocality_from_measure wightmanCovariance_from_measure
          wightmanSpectrumCondition_from_measure).axioms) :
    let C :=
      (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathExactGapConstructionSpineOfReconstruction
        W s D wightmanLocality wightmanCovariance
        wightmanSpectrumCondition wightmanLocality_from_measure
        wightmanCovariance_from_measure wightmanSpectrumCondition_from_measure
        definitionBridge definitionBridge_uses_measure_axioms).toConstructionSpine.toUnconditionalTarget
    C.toPipeline.definitionBridge.spine.model.hasMassGap ∧
      0 < exactGapValueReal ∧
      exactGapValueReal = sInf C.toPipeline.nonVacuumHamiltonianSpectrum := by
  exact finite_wilson_explicit_canonical_gauge_singleLinkHeatBath_mass_gap
    W s D
    (finiteWilsonExplicitCanonicalGaugeSingleLinkHeatBathMeasureBridge W s D
      wightmanLocality wightmanCovariance wightmanSpectrumCondition
      wightmanLocality_from_measure wightmanCovariance_from_measure
      wightmanSpectrumCondition_from_measure)
    rfl definitionBridge definitionBridge_uses_measure_axioms

end

end MathlibAnalytic
end MGAP4D
