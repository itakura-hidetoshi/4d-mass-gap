import MGAP4D.MathlibAnalytic.OSWightmanMassGapDefinitionBridge

namespace MGAP4D
namespace MathlibAnalytic

/-- Euclidean Yang--Mills measure-side data feeding the OS/Wightman route.

This is intentionally a conditional Mathlib-facing interface.  The field
`euclideanMeasure` is a genuine Mathlib measure on the displayed configuration
space, while the analytic properties are kept as propositions that a concrete
Yang--Mills construction must prove. -/
structure EuclideanYangMillsMeasurePackage where
  configurationSpace : Type
  [instMeasurableSpace : MeasurableSpace configurationSpace]
  euclideanMeasure : MeasureTheory.Measure configurationSpace
  gaugeGroup : Type
  fieldAlgebra : Type
  schwingerFunctions : ℕ → Type
  gaugeGroupCompact : Prop
  gaugeGroupNontrivial : Prop
  reflectionPositive : Prop
  euclideanInvariant : Prop
  symmetric : Prop
  clusterProperty : Prop
  regularity : Prop

/-- Readiness of the Euclidean measure package: the Euclidean measure has supplied
exactly the OS-side analytic properties needed for reconstruction. -/
def EuclideanYangMillsMeasurePackage.ready
    (μ : EuclideanYangMillsMeasurePackage) : Prop :=
  μ.gaugeGroupCompact ∧
  μ.gaugeGroupNontrivial ∧
  μ.reflectionPositive ∧
  μ.euclideanInvariant ∧
  μ.symmetric ∧
  μ.clusterProperty ∧
  μ.regularity

/-- Extract gauge compactness from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_gauge_group_compact
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.gaugeGroupCompact := by
  rcases hμ with ⟨hCompact, _hNontrivial, _hReflection, _hInvariant,
    _hSymmetric, _hCluster, _hRegularity⟩
  exact hCompact

/-- Extract gauge nontriviality from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_gauge_group_nontrivial
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.gaugeGroupNontrivial := by
  rcases hμ with ⟨_hCompact, hNontrivial, _hReflection, _hInvariant,
    _hSymmetric, _hCluster, _hRegularity⟩
  exact hNontrivial

/-- Extract reflection positivity from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_reflection_positive
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.reflectionPositive := by
  rcases hμ with ⟨_hCompact, _hNontrivial, hReflection, _hInvariant,
    _hSymmetric, _hCluster, _hRegularity⟩
  exact hReflection

/-- Extract Euclidean invariance from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_euclidean_invariant
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.euclideanInvariant := by
  rcases hμ with ⟨_hCompact, _hNontrivial, _hReflection, hInvariant,
    _hSymmetric, _hCluster, _hRegularity⟩
  exact hInvariant

/-- Extract OS symmetry from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_symmetric
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.symmetric := by
  rcases hμ with ⟨_hCompact, _hNontrivial, _hReflection, _hInvariant,
    hSymmetric, _hCluster, _hRegularity⟩
  exact hSymmetric

/-- Extract the OS cluster property from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_cluster_property
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.clusterProperty := by
  rcases hμ with ⟨_hCompact, _hNontrivial, _hReflection, _hInvariant,
    _hSymmetric, hCluster, _hRegularity⟩
  exact hCluster

/-- Extract OS regularity from Euclidean measure readiness. -/
theorem euclidean_yang_mills_measure_ready_regularity
    (μ : EuclideanYangMillsMeasurePackage) (hμ : μ.ready) :
    μ.regularity := by
  rcases hμ with ⟨_hCompact, _hNontrivial, _hReflection, _hInvariant,
    _hSymmetric, _hCluster, hRegularity⟩
  exact hRegularity

/-- Bridge from a Euclidean Yang--Mills measure package to the named
Osterwalder--Schrader and Wightman assumption package.

The OS reconstruction theorem is represented here by typed maps from the
Euclidean measure-side hypotheses to the Wightman-side hypotheses.  Thus the
bridge is explicit and auditable rather than hidden behind a receipt. -/
structure EuclideanYangMillsMeasureToOSWightmanBridge where
  measure : EuclideanYangMillsMeasurePackage
  axioms : OSWightmanYangMillsAxioms
  gaugeGroup_identified : axioms.gaugeGroup = measure.gaugeGroup
  fieldAlgebra_identified : axioms.fieldAlgebra = measure.fieldAlgebra
  euclideanConfigurationSpace_identified :
    axioms.euclideanFieldConfigurations = measure.configurationSpace
  schwingerFunctions_identified : axioms.schwingerFunctions = measure.schwingerFunctions
  gaugeGroupCompact_from_measure : measure.gaugeGroupCompact → axioms.gaugeGroupCompact
  gaugeGroupNontrivial_from_measure :
    measure.gaugeGroupNontrivial → axioms.gaugeGroupNontrivial
  osReflectionPositive_from_measure : measure.reflectionPositive → axioms.osReflectionPositive
  osEuclideanInvariant_from_measure : measure.euclideanInvariant → axioms.osEuclideanInvariant
  osSymmetric_from_measure : measure.symmetric → axioms.osSymmetric
  osClusterProperty_from_measure : measure.clusterProperty → axioms.osClusterProperty
  osRegularity_from_measure : measure.regularity → axioms.osRegularity
  wightmanLocality_from_os_reconstruction : measure.ready → axioms.wightmanLocality
  wightmanCovariance_from_os_reconstruction : measure.ready → axioms.wightmanCovariance
  wightmanSpectrumCondition_from_os_reconstruction :
    measure.ready → axioms.wightmanSpectrumCondition

/-- The Euclidean measure-to-OS/Wightman bridge proves readiness of the
OS/Wightman assumption package. -/
theorem euclidean_yang_mills_measure_to_os_wightman_ready
    (E : EuclideanYangMillsMeasureToOSWightmanBridge)
    (hμ : E.measure.ready) :
    E.axioms.ready := by
  unfold OSWightmanYangMillsAxioms.ready
  exact ⟨
    E.gaugeGroupCompact_from_measure
      (euclidean_yang_mills_measure_ready_gauge_group_compact E.measure hμ),
    E.gaugeGroupNontrivial_from_measure
      (euclidean_yang_mills_measure_ready_gauge_group_nontrivial E.measure hμ),
    E.osReflectionPositive_from_measure
      (euclidean_yang_mills_measure_ready_reflection_positive E.measure hμ),
    E.osEuclideanInvariant_from_measure
      (euclidean_yang_mills_measure_ready_euclidean_invariant E.measure hμ),
    E.osSymmetric_from_measure
      (euclidean_yang_mills_measure_ready_symmetric E.measure hμ),
    E.osClusterProperty_from_measure
      (euclidean_yang_mills_measure_ready_cluster_property E.measure hμ),
    E.osRegularity_from_measure
      (euclidean_yang_mills_measure_ready_regularity E.measure hμ),
    E.wightmanLocality_from_os_reconstruction hμ,
    E.wightmanCovariance_from_os_reconstruction hμ,
    E.wightmanSpectrumCondition_from_os_reconstruction hμ⟩

/-- A single end-to-end pipeline from Euclidean Yang--Mills measure data to the
Hamiltonian/PVM mass-gap definition bridge.

This structure does not assert that such a pipeline exists unconditionally; it
states the exact object that a concrete construction must provide. -/
structure EuclideanYangMillsMeasureMassGapPipeline where
  euclideanToOSWightman : EuclideanYangMillsMeasureToOSWightmanBridge
  definitionBridge : OSWightmanMassGapDefinitionBridge
  measureReady : euclideanToOSWightman.measure.ready
  bridge_uses_reconstructed_axioms :
    definitionBridge.spine.axioms = euclideanToOSWightman.axioms

/-- The Hamiltonian non-vacuum spectral surface: spectrum of `H` away from the
vacuum energy.  This is the audit-visible proxy for the spectrum of `H` on the
orthogonal complement of the vacuum sector. -/
def EuclideanYangMillsMeasureMassGapPipeline.nonVacuumHamiltonianSpectrum
    (P : EuclideanYangMillsMeasureMassGapPipeline) : Set ℝ :=
  P.definitionBridge.spine.model.energySpectrum \ ({0} : Set ℝ)

/-- The vacuum vector Ω of the reconstructed physical Hilbert space. -/
def EuclideanYangMillsMeasureMassGapPipeline.vacuumOmega
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.model.H :=
  P.definitionBridge.spine.model.vacuum

/-- The upstream Euclidean measure package proves the downstream OS/Wightman
assumption package used by the bridge. -/
theorem euclidean_yang_mills_measure_pipeline_os_axioms_ready
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.axioms.ready := by
  have hUpstream : P.euclideanToOSWightman.axioms.ready :=
    euclidean_yang_mills_measure_to_os_wightman_ready
      P.euclideanToOSWightman P.measureReady
  rw [P.bridge_uses_reconstructed_axioms]
  exact hUpstream

/-- The OS reconstruction gives readiness of the reconstructed model's
OS/Wightman package. -/
theorem euclidean_yang_mills_measure_pipeline_reconstructed_model_ready
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.model.osWightman.ready := by
  exact os_wightman_reconstruction_model_ready P.definitionBridge.spine

/-- The Wightman theory obtained from OS reconstruction has locality, covariance,
and the spectrum condition. -/
theorem euclidean_yang_mills_measure_pipeline_wightman_theory
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.axioms.wightmanLocality ∧
    P.definitionBridge.spine.axioms.wightmanCovariance ∧
    P.definitionBridge.spine.axioms.wightmanSpectrumCondition := by
  have hReady : P.definitionBridge.spine.axioms.ready :=
    euclidean_yang_mills_measure_pipeline_os_axioms_ready P
  exact ⟨
    os_wightman_ready_locality P.definitionBridge.spine.axioms hReady,
    os_wightman_ready_covariance P.definitionBridge.spine.axioms hReady,
    os_wightman_ready_spectrum_condition P.definitionBridge.spine.axioms hReady⟩

/-- The reconstructed physical Hilbert space is nonempty because it contains the
vacuum vector. -/
theorem euclidean_yang_mills_measure_pipeline_physical_hilbert_space
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    Nonempty P.definitionBridge.spine.model.H := by
  exact axiomatic_yang_mills_reconstructed_hilbert_nonempty
    P.definitionBridge.spine.model

/-- The Hamiltonian is the self-adjoint time-translation generator supplied by
the definition bridge. -/
theorem euclidean_yang_mills_measure_pipeline_hamiltonian_time_translation_generator
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.model.hamiltonianSelfAdjoint := by
  exact P.definitionBridge.hamiltonianSelfAdjoint_proof

/-- The reconstructed vacuum Ω is the spectral point at energy zero. -/
theorem euclidean_yang_mills_measure_pipeline_vacuum_omega_spectral_point
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.vacuumOmega ∈ P.definitionBridge.spine.model.spectralPVM ({0} : Set ℝ) := by
  unfold EuclideanYangMillsMeasureMassGapPipeline.vacuumOmega
  exact P.definitionBridge.vacuumSpectralPoint

/-- Positive energy for the Hamiltonian spectrum follows from the Wightman
spectrum condition through the definition bridge. -/
theorem euclidean_yang_mills_measure_pipeline_positive_hamiltonian_spectrum
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    ∀ E : ℝ, E ∈ P.definitionBridge.spine.model.energySpectrum → 0 ≤ E := by
  exact os_wightman_bridge_positive_energy P.definitionBridge

/-- The exact normalized gap is the infimum of the non-vacuum Hamiltonian
spectrum. -/
theorem euclidean_yang_mills_measure_pipeline_nonvacuum_spectrum_threshold
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    exactGapValueReal = sInf P.nonVacuumHamiltonianSpectrum := by
  unfold EuclideanYangMillsMeasureMassGapPipeline.nonVacuumHamiltonianSpectrum
  exact os_wightman_bridge_exact_gap_spectral_threshold P.definitionBridge

/-- The end-to-end Euclidean measure → OS axioms → OS reconstruction → Wightman
Theory → Hilbert space → Hamiltonian → vacuum → non-vacuum spectrum route gives
`Δ > 0`, expressed by the repository's normalized exact-gap carrier. -/
theorem euclidean_yang_mills_measure_pipeline_delta_positive
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    0 < exactGapValueReal := by
  exact os_wightman_bridge_exact_gap_positive P.definitionBridge

/-- Main end-to-end conditional theorem: a concrete Euclidean Yang--Mills measure
pipeline with the displayed OS/Wightman reconstruction and Hamiltonian/PVM bridge
has a positive mass gap, and the positive gap is the non-vacuum Hamiltonian
spectral threshold. -/
theorem euclidean_yang_mills_measure_os_reconstruction_wightman_hamiltonian_mass_gap
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    P.definitionBridge.spine.model.hasMassGap ∧
    0 < exactGapValueReal ∧
    exactGapValueReal = sInf P.nonVacuumHamiltonianSpectrum := by
  exact ⟨
    os_wightman_bridge_mass_gap_definition P.definitionBridge,
    euclidean_yang_mills_measure_pipeline_delta_positive P,
    euclidean_yang_mills_measure_pipeline_nonvacuum_spectrum_threshold P⟩

/-- Certificate bundling the complete theorem-level chain.  Every field is an
ordinary proposition over Mathlib data: a measure, an OS/Wightman assumption
package, a reconstructed Hilbert carrier, a Hamiltonian, a vacuum vector, and the
non-vacuum spectral threshold. -/
structure EuclideanYangMillsMeasureToMassGapPipelineCertificate
    (P : EuclideanYangMillsMeasureMassGapPipeline) where
  measureReady : P.euclideanToOSWightman.measure.ready
  osAxiomsReady : P.definitionBridge.spine.axioms.ready
  reconstructedModelReady : P.definitionBridge.spine.model.osWightman.ready
  wightmanTheory :
    P.definitionBridge.spine.axioms.wightmanLocality ∧
    P.definitionBridge.spine.axioms.wightmanCovariance ∧
    P.definitionBridge.spine.axioms.wightmanSpectrumCondition
  physicalHilbertSpace : Nonempty P.definitionBridge.spine.model.H
  hamiltonianTimeTranslationGenerator :
    P.definitionBridge.spine.model.hamiltonianSelfAdjoint
  vacuumOmegaSpectralPoint :
    P.vacuumOmega ∈ P.definitionBridge.spine.model.spectralPVM ({0} : Set ℝ)
  positiveHamiltonianSpectrum :
    ∀ E : ℝ, E ∈ P.definitionBridge.spine.model.energySpectrum → 0 ≤ E
  nonVacuumSpectralThreshold :
    exactGapValueReal = sInf P.nonVacuumHamiltonianSpectrum
  massGapTheorem : P.definitionBridge.spine.model.hasMassGap
  deltaPositive : 0 < exactGapValueReal

/-- Construct the full Euclidean-measure-to-positive-gap certificate. -/
def euclideanYangMillsMeasureToMassGapPipelineCertificate
    (P : EuclideanYangMillsMeasureMassGapPipeline) :
    EuclideanYangMillsMeasureToMassGapPipelineCertificate P :=
  { measureReady := P.measureReady
    osAxiomsReady := euclidean_yang_mills_measure_pipeline_os_axioms_ready P
    reconstructedModelReady :=
      euclidean_yang_mills_measure_pipeline_reconstructed_model_ready P
    wightmanTheory := euclidean_yang_mills_measure_pipeline_wightman_theory P
    physicalHilbertSpace :=
      euclidean_yang_mills_measure_pipeline_physical_hilbert_space P
    hamiltonianTimeTranslationGenerator :=
      euclidean_yang_mills_measure_pipeline_hamiltonian_time_translation_generator P
    vacuumOmegaSpectralPoint :=
      euclidean_yang_mills_measure_pipeline_vacuum_omega_spectral_point P
    positiveHamiltonianSpectrum :=
      euclidean_yang_mills_measure_pipeline_positive_hamiltonian_spectrum P
    nonVacuumSpectralThreshold :=
      euclidean_yang_mills_measure_pipeline_nonvacuum_spectrum_threshold P
    massGapTheorem := os_wightman_bridge_mass_gap_definition P.definitionBridge
    deltaPositive := euclidean_yang_mills_measure_pipeline_delta_positive P }

end MathlibAnalytic
end MGAP4D
