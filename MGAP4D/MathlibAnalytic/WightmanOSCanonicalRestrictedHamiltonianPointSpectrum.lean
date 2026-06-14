import MGAP4D.MathlibAnalytic.EuclideanYangMillsCanonicalRestrictedHamiltonianGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The real point spectrum of a partially-defined real-linear operator: those
real numbers admitting a nonzero eigenvector in the operator domain. -/
def LinearPMap.realPointSpectrum
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →ₗ.[ℝ] E) : Set ℝ :=
  {λ | ∃ x : T.domain, (x : E) ≠ 0 ∧ T x = λ • (x : E)}

/-- The point spectrum of the actual canonical Hamiltonian restriction to
`Ω⊥`. -/
def ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalPointSpectrum
    (M : ExplicitWightmanOSReconstructedModel) : Set ℝ :=
  M.canonicalVacuumOrthogonalHamiltonian.realPointSpectrum

/-- Membership in the canonical point spectrum is exactly existence of a
nonzero domain eigenvector. -/
theorem mem_canonical_vacuum_orthogonal_pointSpectrum_iff
    (M : ExplicitWightmanOSReconstructedModel) (λ : ℝ) :
    λ ∈ M.canonicalVacuumOrthogonalPointSpectrum ↔
      ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        (x : M.VacuumOrthogonalHilbert) ≠ 0 ∧
          M.canonicalVacuumOrthogonalHamiltonian x =
            λ • (x : M.VacuumOrthogonalHilbert) := by
  rfl

/-- Spectral identification input connecting the actual operator point spectrum
with the non-vacuum physical spectral set already obtained from the PVM route.
This is kept explicit because the current Mathlib `LinearPMap` API does not
supply an unbounded-operator spectral theorem. -/
structure ExplicitWightmanOSCanonicalPointSpectrumBridge
    (M : ExplicitWightmanOSReconstructedModel) extends
      ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M where
  pointSpectrum_eq_restrictedSpectrum :
    M.canonicalVacuumOrthogonalPointSpectrum = restrictedSpectrum

/-- The canonical point spectrum excludes the vacuum energy. -/
theorem canonical_vacuum_orthogonal_pointSpectrum_zero_not_mem
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPointSpectrumBridge M) :
    0 ∉ M.canonicalVacuumOrthogonalPointSpectrum := by
  rw [B.pointSpectrum_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_zero_not_mem
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge

/-- Every eigenvalue of the actual canonical restriction lies above any proven
Hamiltonian mass gap. -/
theorem canonical_vacuum_orthogonal_pointSpectrum_lower_bound
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPointSpectrumBridge M)
    {m : ℝ} (hGap : M.HasMassGap m) :
    M.canonicalVacuumOrthogonalPointSpectrum ⊆ Set.Ici m := by
  rw [B.pointSpectrum_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_subset_Ici
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    hGap

/-- When the lower edge is attained, the infimum of the actual point spectrum is
the mass-gap value. -/
theorem canonical_vacuum_orthogonal_pointSpectrum_sInf_eq
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSCanonicalPointSpectrumBridge M)
    {m : ℝ} (hGap : M.HasMassGap m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    sInf M.canonicalVacuumOrthogonalPointSpectrum = m := by
  rw [B.pointSpectrum_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_sInf_eq
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    hGap hmSpectrum

/-- Euclidean finite-volume clustering yields a positive lower bound on every
actual eigenvalue of `H|Ω⊥`. -/
theorem euclidean_clustering_canonical_pointSpectrum_lower_bound
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalPointSpectrumBridge C.explicitModel) :
    0 < exactGapValueReal ∧
      C.explicitModel.canonicalVacuumOrthogonalPointSpectrum ⊆
        Set.Ici exactGapValueReal := by
  have hGap : C.explicitModel.HasMassGap exactGapValueReal :=
    euclidean_finite_volume_clustering_mass_gap C A T E S F
  exact ⟨hGap.1,
    canonical_vacuum_orthogonal_pointSpectrum_lower_bound B hGap⟩

/-- Exact-value specialization for the actual point spectrum. -/
theorem euclidean_clustering_canonical_pointSpectrum_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalPointSpectrumBridge C.explicitModel)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      C.explicitModel.canonicalVacuumOrthogonalPointSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf C.explicitModel.canonicalVacuumOrthogonalPointSpectrum =
        exactGapValueReal := by
  have hGap : C.explicitModel.HasMassGap exactGapValueReal :=
    euclidean_finite_volume_clustering_mass_gap C A T E S F
  exact ⟨hGap.1,
    canonical_vacuum_orthogonal_pointSpectrum_lower_bound B hGap,
    canonical_vacuum_orthogonal_pointSpectrum_sInf_eq
      B hGap hExactSpectrum⟩

end

end MathlibAnalytic
end MGAP4D
