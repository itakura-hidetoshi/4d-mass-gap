import MGAP4D.MathlibAnalytic.AxiomaticYangMillsExactGapSpectralCore
import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMMeasureConstruction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Construct the dependency-reduced exact-gap spectral core from the repository's
fully typed explicit Wightman/OS reconstructed model.

The partial Hamiltonian is retained by zero extension away from its Mathlib
operator domain.  The legacy set-valued spectral interface is the fixed-point
range of the actual bounded PVM projection.  Thus the reduced core is connected
to the displayed physical Hilbert space, Hamiltonian, vacuum, PVM, and joint
energy-momentum spectrum rather than populated by unrelated carriers.
-/

/-- Convert a four-momentum to the legacy energy/spatial-momentum pair. -/
def MinkowskiMomentum.toLegacyEnergyMomentumPair
    (p : MinkowskiMomentum) : ℝ × (Fin 3 → ℝ) :=
  (p.energy, fun i => p i.succ)

/-- The explicit joint spectrum in the pair carrier used by the reduced core. -/
def ExplicitWightmanOSReconstructedModel.legacyEnergyMomentumSpectrum
    (M : ExplicitWightmanOSReconstructedModel) :
    Set (ℝ × (Fin 3 → ℝ)) :=
  MinkowskiMomentum.toLegacyEnergyMomentumPair '' M.energyMomentumSpectrum

/-- Totalize the actual partially defined Hamiltonian by zero away from its
Mathlib operator domain.  On the physical domain this is exactly the original
Hamiltonian action. -/
def ExplicitWightmanOSReconstructedModel.hamiltonianZeroExtension
    (M : ExplicitWightmanOSReconstructedModel) : M.H → M.H :=
  fun ψ =>
    if hψ : ψ ∈ M.hamiltonian.domain then
      M.hamiltonian ⟨ψ, hψ⟩
    else
      0

@[simp]
theorem ExplicitWightmanOSReconstructedModel.hamiltonianZeroExtension_of_mem
    (M : ExplicitWightmanOSReconstructedModel)
    (ψ : M.H) (hψ : ψ ∈ M.hamiltonian.domain) :
    M.hamiltonianZeroExtension ψ = M.hamiltonian ⟨ψ, hψ⟩ := by
  simp [ExplicitWightmanOSReconstructedModel.hamiltonianZeroExtension, hψ]

@[simp]
theorem ExplicitWightmanOSReconstructedModel.hamiltonianZeroExtension_of_not_mem
    (M : ExplicitWightmanOSReconstructedModel)
    (ψ : M.H) (hψ : ψ ∉ M.hamiltonian.domain) :
    M.hamiltonianZeroExtension ψ = 0 := by
  simp [ExplicitWightmanOSReconstructedModel.hamiltonianZeroExtension, hψ]

/-- Set-valued spectral carrier obtained as the fixed-point range of the actual
bounded PVM projection. -/
def ExplicitWightmanOSReconstructedModel.spectralProjectionFixedPoints
    (M : ExplicitWightmanOSReconstructedModel)
    (s : Set ℝ) : Set M.H :=
  {ψ | M.spectralPVM.projection s ψ = ψ}

/-- The reconstructed vacuum belongs to the zero-energy PVM fixed-point range. -/
theorem ExplicitWightmanOSReconstructedModel.vacuum_mem_zeroProjectionFixedPoints
    (M : ExplicitWightmanOSReconstructedModel) :
    M.vacuum ∈ M.spectralProjectionFixedPoints ({0} : Set ℝ) := by
  exact M.vacuumSpectralProjection

/-- Construct the reduced exact-gap spectral core from the explicit reconstructed
model, an exact Hamiltonian gap theorem, and threshold attainment. -/
noncomputable def ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    FourDimensionalYangMillsExactGapSpectralCore :=
  { osWightman := M.axioms.toLegacy
    spacetimeDim := 4
    spacetimeDim_eq_four := rfl
    H := M.H
    instNormedAddCommGroup := M.hilbertNormedAddCommGroup
    instInnerProductSpace := M.hilbertInnerProductSpace
    instCompleteSpace := M.hilbertCompleteSpace
    vacuum := M.vacuum
    hamiltonian := M.hamiltonianZeroExtension
    spectralPVM := M.spectralProjectionFixedPoints
    energySpectrum := M.hamiltonianEnergySpectrum
    energyMomentumSpectrum := M.legacyEnergyMomentumSpectrum
    hamiltonianSelfAdjoint := IsSelfAdjoint M.hamiltonian
    exactHamiltonianMassGap := hGap
    exactGapAttained := hExactSpectrum }

@[simp]
theorem ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore_energySpectrum
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    (M.toExactGapSpectralCore hGap hExactSpectrum).energySpectrum =
      M.hamiltonianEnergySpectrum :=
  rfl

@[simp]
theorem ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore_vacuum
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    (M.toExactGapSpectralCore hGap hExactSpectrum).vacuum = M.vacuum :=
  rfl

/-- The reduced core's self-adjointness proposition is discharged by the actual
Mathlib `LinearPMap.IsSelfAdjoint` theorem stored in the explicit model. -/
theorem ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore_selfAdjoint
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    (M.toExactGapSpectralCore hGap hExactSpectrum).hamiltonianSelfAdjoint := by
  change IsSelfAdjoint M.hamiltonian
  exact M.hamiltonianSelfAdjoint

/-- On the displayed Hamiltonian domain, the core Hamiltonian is exactly the
physical partially defined Hamiltonian. -/
theorem ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore_hamiltonian_of_mem
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (ψ : M.H) (hψ : ψ ∈ M.hamiltonian.domain) :
    (M.toExactGapSpectralCore hGap hExactSpectrum).hamiltonian ψ =
      M.hamiltonian ⟨ψ, hψ⟩ := by
  exact M.hamiltonianZeroExtension_of_mem ψ hψ

/-- The core's set-valued PVM is definitionally the fixed-point range of the
actual bounded projection. -/
theorem ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore_pvm_mem_iff
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (s : Set ℝ) (ψ : M.H) :
    ψ ∈ (M.toExactGapSpectralCore hGap hExactSpectrum).spectralPVM s ↔
      M.spectralPVM.projection s ψ = ψ := by
  rfl

/-- The zero-energy vacuum spectral point is generated from the actual vacuum
projection theorem. -/
theorem ExplicitWightmanOSReconstructedModel.toExactGapSpectralCore_vacuumSpectralPoint
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    (M.toExactGapSpectralCore hGap hExactSpectrum).vacuum ∈
      (M.toExactGapSpectralCore hGap hExactSpectrum).spectralPVM
        ({0} : Set ℝ) := by
  exact M.vacuum_mem_zeroProjectionFixedPoints

/-- A relativistic exact gap in the displayed joint spectrum constructs the
reduced exact-gap spectral core directly. -/
noncomputable def
    ExplicitWightmanOSReconstructedModel.toExactGapSpectralCoreOfRelativisticGap
    (M : ExplicitWightmanOSReconstructedModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    FourDimensionalYangMillsExactGapSpectralCore :=
  M.toExactGapSpectralCore
    (explicit_wightman_os_reconstruction_has_mass_gap M hRelGap)
    hExactSpectrum

section QuadraticPVMSemigroup

variable
  (C : EuclideanYangMillsConnectedObservableCore)
  (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
  (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
  (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
  (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
    C.explicitModel A.toScalarSpectralRealization T)
  (X : EuclideanYangMillsExponentialClusteringEstimate C)

/-- The constructed quadratic PVM scalar measures, OS semigroup spectral
formula, and Euclidean clustering produce the exact-gap spectral core. -/
noncomputable def euclideanYangMillsQuadraticPVMExactGapSpectralCore
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    FourDimensionalYangMillsExactGapSpectralCore :=
  C.explicitModel.toExactGapSpectralCore
    (euclidean_quadratic_pvm_semigroup_clustering_mass_gap C A T E S X)
    hExactSpectrum

/-- The Euclidean analytic construction retains the actual Hamiltonian
self-adjointness theorem inside the generated core. -/
theorem euclideanYangMillsQuadraticPVMExactGapSpectralCore_selfAdjoint
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    (euclideanYangMillsQuadraticPVMExactGapSpectralCore
      C A T E S X hExactSpectrum).hamiltonianSelfAdjoint := by
  exact C.explicitModel.toExactGapSpectralCore_selfAdjoint
    (euclidean_quadratic_pvm_semigroup_clustering_mass_gap C A T E S X)
    hExactSpectrum

/-- The Euclidean analytic construction generates the exact non-vacuum spectral
threshold identity through the reduced core. -/
theorem euclideanYangMillsQuadraticPVMExactGapSpectralCore_threshold
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    sInf
        ((euclideanYangMillsQuadraticPVMExactGapSpectralCore
          C A T E S X hExactSpectrum).energySpectrum \ ({0} : Set ℝ)) =
      exactGapValueReal := by
  exact
    (euclideanYangMillsQuadraticPVMExactGapSpectralCore
      C A T E S X hExactSpectrum).sInfNonvacuumEqExactGap

end QuadraticPVMSemigroup

/-- Compact theorem surface recording that the generated core remains tied to the
actual explicit Hamiltonian, vacuum PVM point, and exact spectral threshold. -/
abbrev ExplicitWightmanOSExactGapSpectralCorePhysicalProp
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) : Prop :=
  let core := M.toExactGapSpectralCore hGap hExactSpectrum
  core.hamiltonianSelfAdjoint ∧
    core.vacuum ∈ core.spectralPVM ({0} : Set ℝ) ∧
    core.energySpectrum = M.hamiltonianEnergySpectrum ∧
    (∀ (ψ : M.H) (hψ : ψ ∈ M.hamiltonian.domain),
      core.hamiltonian ψ = M.hamiltonian ⟨ψ, hψ⟩) ∧
    IsLeast (core.energySpectrum \ ({0} : Set ℝ)) exactGapValueReal

/-- The physical identifications and exact lower-edge theorem hold
simultaneously for the generated core. -/
theorem explicitWightmanOSExactGapSpectralCore_physical
    (M : ExplicitWightmanOSReconstructedModel)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapSpectralCorePhysicalProp
      M hGap hExactSpectrum := by
  refine ⟨
    M.toExactGapSpectralCore_selfAdjoint hGap hExactSpectrum,
    M.toExactGapSpectralCore_vacuumSpectralPoint hGap hExactSpectrum,
    rfl,
    ?_,
    (M.toExactGapSpectralCore hGap hExactSpectrum).exactGapIsLeast⟩
  intro ψ hψ
  exact M.toExactGapSpectralCore_hamiltonian_of_mem
    hGap hExactSpectrum ψ hψ

end

end MathlibAnalytic
end MGAP4D
