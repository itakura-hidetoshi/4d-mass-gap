import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertConstruction
import MGAP4D.MathlibAnalytic.WightmanOSExplicitEnergyMomentumMassGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A reconstructed Yang--Mills model whose Hilbert carrier is definitionally the
OS null-quotient completion constructed from the Euclidean measure.

The inner-product instance depends on the complete positive-time observable
package, which cannot be reconstructed from the abbreviated carrier type alone.
It is therefore installed explicitly at the self-adjointness boundary. -/
structure EuclideanYangMillsOSPhysicalHilbertReconstructedModel
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) where
  observables : EuclideanYangMillsOSPositiveTimeObservableConstruction S
  axioms : ExplicitOSWightmanFieldAxioms
  axioms_toLegacy_identified :
    axioms.toLegacy = S.definitionBridge.spine.axioms
  field : axioms.TestFunction →
    observables.PhysicalHilbert →ₗ.[ℝ] observables.PhysicalHilbert
  hamiltonian :
    observables.PhysicalHilbert →ₗ.[ℝ] observables.PhysicalHilbert
  hamiltonianSelfAdjoint :
    letI : InnerProductSpace ℝ observables.PhysicalHilbert :=
      os_physical_hilbert_innerProductSpace observables
    letI : CompleteSpace observables.PhysicalHilbert :=
      os_physical_hilbert_complete observables
    IsSelfAdjoint hamiltonian
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

def EuclideanYangMillsOSPhysicalHilbertReconstructedModel.toExplicitModel
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    ExplicitWightmanOSReconstructedModel := by
  letI : InnerProductSpace ℝ M.observables.PhysicalHilbert :=
    os_physical_hilbert_innerProductSpace M.observables
  letI : CompleteSpace M.observables.PhysicalHilbert :=
    os_physical_hilbert_complete M.observables
  exact
    { axioms := M.axioms
      H := M.observables.PhysicalHilbert
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

theorem os_physical_reconstructed_model_hilbert_identified
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.H = M.observables.PhysicalHilbert := by
  rfl

theorem os_physical_reconstructed_model_complete
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    CompleteSpace M.toExplicitModel.H := by
  infer_instance

theorem os_physical_reconstructed_model_vacuum_eq_os_class
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.vacuum = M.observables.vacuum :=
  M.vacuum_eq_os_vacuum

theorem os_physical_reconstructed_model_uses_continuum_axioms
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.axioms.toLegacy =
      S.definitionBridge.spine.axioms :=
  M.axioms_toLegacy_identified

theorem os_physical_reconstructed_model_has_mass_gap
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    {m : ℝ}
    (hGap : HasRelativisticMassGap M.energyMomentumSpectrum m) :
    M.toExplicitModel.HasMassGap m := by
  exact explicit_wightman_os_reconstruction_has_mass_gap M.toExplicitModel hGap

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
    hamiltonianSelfAdjoint := M.toExplicitModel.hamiltonianSelfAdjoint }

end

end MathlibAnalytic
end MGAP4D
