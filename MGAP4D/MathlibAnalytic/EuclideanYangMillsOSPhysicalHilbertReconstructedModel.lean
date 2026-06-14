import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertConstruction
import MGAP4D.MathlibAnalytic.WightmanOSExplicitEnergyMomentumMassGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A reconstructed Yang--Mills model whose Hilbert carrier is definitionally the
OS null-quotient completion constructed from the Euclidean measure.

Unlike `ExplicitWightmanOSReconstructedModel`, the Hilbert type is not an
independent input here.  It is fixed to
`Completion (SeparationQuotient PositiveTimeObservable)`. -/
structure EuclideanYangMillsOSPhysicalHilbertReconstructedModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  observables : EuclideanYangMillsOSPositiveTimeObservableConstruction S
  [physicalNormedAddCommGroup :
    NormedAddCommGroup observables.PhysicalHilbert]
  [physicalInnerProductSpace :
    InnerProductSpace ℝ observables.PhysicalHilbert]
  [physicalCompleteSpace : CompleteSpace observables.PhysicalHilbert]
  axioms : ExplicitOSWightmanFieldAxioms
  axioms_toLegacy_identified :
    axioms.toLegacy = S.definitionBridge.spine.axioms
  field : axioms.TestFunction →
    observables.PhysicalHilbert →ₗ.[ℝ] observables.PhysicalHilbert
  hamiltonian :
    observables.PhysicalHilbert →ₗ.[ℝ] observables.PhysicalHilbert
  hamiltonianSelfAdjoint : IsSelfAdjoint hamiltonian
  vacuum : observables.PhysicalHilbert
  vacuum_eq_os_vacuum : vacuum = observables.vacuum
  vacuum_norm : ‖vacuum‖ = 1
  vacuum_mem_hamiltonianDomain : vacuum ∈ hamiltonian.domain
  vacuumEnergyZero :
    hamiltonian ⟨vacuum, vacuum_mem_hamiltonianDomain⟩ = 0
  spectralPVM :
    OrthogonalProjectionValuedSetFunction observables.PhysicalHilbert
  vacuumSpectralProjection :
    spectralPVM.projection ({0} : Set ℝ) vacuum = vacuum
  energyMomentumSpectrum : Set MinkowskiMomentum
  spectrumCondition : ∀ p ∈ energyMomentumSpectrum, p.InForwardCone
  hamiltonianEnergySpectrum : Set ℝ
  energySpectrum_eq_projection :
    hamiltonianEnergySpectrum = energyProjection energyMomentumSpectrum

attribute [instance]
  EuclideanYangMillsOSPhysicalHilbertReconstructedModel.physicalNormedAddCommGroup
  EuclideanYangMillsOSPhysicalHilbertReconstructedModel.physicalInnerProductSpace
  EuclideanYangMillsOSPhysicalHilbertReconstructedModel.physicalCompleteSpace

/-- Forgetful projection to the existing explicit reconstructed-model interface.
The projected Hilbert carrier is definitionally the OS physical completion. -/
def EuclideanYangMillsOSPhysicalHilbertReconstructedModel.toExplicitModel
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    ExplicitWightmanOSReconstructedModel :=
  { axioms := M.axioms
    H := M.observables.PhysicalHilbert
    hilbertNormedAddCommGroup := M.physicalNormedAddCommGroup
    hilbertInnerProductSpace := M.physicalInnerProductSpace
    hilbertCompleteSpace := M.physicalCompleteSpace
    field := M.field
    hamiltonian := M.hamiltonian
    hamiltonianSelfAdjoint := M.hamiltonianSelfAdjoint
    vacuum := M.vacuum
    vacuum_norm := M.vacuum_norm
    vacuum_mem_hamiltonianDomain := M.vacuum_mem_hamiltonianDomain
    vacuumEnergyZero := M.vacuumEnergyZero
    spectralPVM := M.spectralPVM
    vacuumSpectralProjection := M.vacuumSpectralProjection
    energyMomentumSpectrum := M.energyMomentumSpectrum
    spectrumCondition := M.spectrumCondition
    hamiltonianEnergySpectrum := M.hamiltonianEnergySpectrum
    energySpectrum_eq_projection := M.energySpectrum_eq_projection }

/-- The existing reconstructed-model Hilbert carrier is now definitionally the
OS quotient completion. -/
theorem os_physical_reconstructed_model_hilbert_identified
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.H = M.observables.PhysicalHilbert := by
  rfl

/-- Completeness of the projected reconstructed-model carrier comes from the OS
completion, not from a separately postulated Hilbert type. -/
theorem os_physical_reconstructed_model_complete
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    CompleteSpace M.toExplicitModel.H := by
  exact M.physicalCompleteSpace

/-- The projected vacuum is the OS class of the constant positive-time
observable. -/
theorem os_physical_reconstructed_model_vacuum_eq_os_class
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.vacuum = M.observables.vacuum :=
  M.vacuum_eq_os_vacuum

/-- The projected model uses exactly the continuum construction's OS/Wightman
axioms. -/
theorem os_physical_reconstructed_model_uses_continuum_axioms
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.axioms.toLegacy =
      S.definitionBridge.spine.axioms :=
  M.axioms_toLegacy_identified

/-- Existing relativistic-to-Hamiltonian mass-gap theorems apply directly to the
OS-constructed physical Hilbert model. -/
theorem os_physical_reconstructed_model_has_mass_gap
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    {m : ℝ}
    (hGap : HasRelativisticMassGap M.energyMomentumSpectrum m) :
    M.toExplicitModel.HasMassGap m := by
  exact explicit_wightman_os_reconstruction_has_mass_gap M.toExplicitModel hGap

/-- Certificate making the distinction from the auxiliary diagonal `ℓ²` model
explicit: the physical carrier is generated from Euclidean observables by OS
quotient completion. -/
structure EuclideanYangMillsOSPhysicalReconstructionCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) where
  hilbertFromOSCompletion :
    M.toExplicitModel.H = M.observables.PhysicalHilbert
  hilbertComplete : CompleteSpace M.toExplicitModel.H
  vacuumFromConstantObservable :
    M.toExplicitModel.vacuum = M.observables.vacuum
  continuumAxiomsIdentified :
    M.toExplicitModel.axioms.toLegacy =
      S.definitionBridge.spine.axioms
  hamiltonianSelfAdjoint : IsSelfAdjoint M.toExplicitModel.hamiltonian

/-- Construct the physical reconstruction certificate. -/
def euclideanYangMillsOSPhysicalReconstructionCertificate
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    EuclideanYangMillsOSPhysicalReconstructionCertificate M :=
  { hilbertFromOSCompletion :=
      os_physical_reconstructed_model_hilbert_identified M
    hilbertComplete := os_physical_reconstructed_model_complete M
    vacuumFromConstantObservable :=
      os_physical_reconstructed_model_vacuum_eq_os_class M
    continuumAxiomsIdentified :=
      os_physical_reconstructed_model_uses_continuum_axioms M
    hamiltonianSelfAdjoint := M.hamiltonianSelfAdjoint }

end

end MathlibAnalytic
end MGAP4D
