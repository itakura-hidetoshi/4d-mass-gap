import MGAP4D.MathlibAnalytic.EuclideanYangMillsFiniteVolumeClusteringLimit
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianSymmetry

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Uniform finite-volume Euclidean clustering produces a strictly positive
spectral lower edge for the actual canonical restricted Hamiltonian.  This route
does not use the legacy first-excitation positivity field or a relativistic-gap
hypothesis. -/
theorem euclidean_clustering_canonical_restricted_hamiltonian_lower_bound
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      C.explicitModel) :
    IsSelfAdjoint C.explicitModel.canonicalVacuumOrthogonalHamiltonian ∧
      Dense ((C.explicitModel.canonicalVacuumOrthogonalHamiltonian.domain :
        Set C.explicitModel.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed
        C.explicitModel.canonicalVacuumOrthogonalHamiltonian ∧
      0 < exactGapValueReal ∧
      B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal := by
  have hGap : HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal :=
    euclidean_finite_volume_clustering_mass_gap C A T E S F
  exact ⟨B.canonicalRestrictedSelfAdjoint,
    canonical_vacuum_orthogonal_hamiltonian_dense_domain B,
    canonical_vacuum_orthogonal_hamiltonian_isClosed B,
    hGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge hGap⟩

/-- If the decay threshold is attained by the Hamiltonian spectrum, the actual
canonical restricted operator has exact physical gap `exactGapValueReal`. -/
theorem euclidean_clustering_canonical_restricted_hamiltonian_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      C.explicitModel)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    IsSelfAdjoint C.explicitModel.canonicalVacuumOrthogonalHamiltonian ∧
      Dense ((C.explicitModel.canonicalVacuumOrthogonalHamiltonian.domain :
        Set C.explicitModel.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed
        C.explicitModel.canonicalVacuumOrthogonalHamiltonian ∧
      0 < exactGapValueReal ∧
      B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal ∧
      sInf B.restrictedSpectrum = exactGapValueReal := by
  have hGap : HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal :=
    euclidean_finite_volume_clustering_mass_gap C A T E S F
  exact ⟨B.canonicalRestrictedSelfAdjoint,
    canonical_vacuum_orthogonal_hamiltonian_dense_domain B,
    canonical_vacuum_orthogonal_hamiltonian_isClosed B,
    hGap.1,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge hGap,
    vacuum_orthogonal_restrictedSpectrum_sInf_eq
      B.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
      hGap hExactSpectrum⟩

/-- End-to-end certificate for the independent route

`finite-volume Euclidean clustering → continuum correlation → scalar spectral
measure → Hamiltonian gap → actual self-adjoint H|Ω⊥`. -/
structure EuclideanYangMillsCanonicalRestrictedHamiltonianGapCertificate
    (C : EuclideanYangMillsConnectedObservableCore)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      C.explicitModel) where
  operatorSelfAdjoint :
    IsSelfAdjoint C.explicitModel.canonicalVacuumOrthogonalHamiltonian
  operatorDomain :
    C.explicitModel.canonicalVacuumOrthogonalHamiltonian.domain =
      C.explicitModel.vacuumOrthogonalHamiltonianDomain
  operatorDomainDense :
    Dense ((C.explicitModel.canonicalVacuumOrthogonalHamiltonian.domain :
      Set C.explicitModel.VacuumOrthogonalHilbert))
  operatorClosed :
    LinearPMap.IsClosed
      C.explicitModel.canonicalVacuumOrthogonalHamiltonian
  spectrumEqNonvacuum :
    B.restrictedSpectrum =
      C.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)
  exactGapPositive : 0 < exactGapValueReal
  spectrumLowerBound :
    B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal
  spectrumInfimum :
    sInf B.restrictedSpectrum = exactGapValueReal

/-- Construct the end-to-end Euclidean/operator certificate. -/
def euclideanYangMillsCanonicalRestrictedHamiltonianGapCertificate
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
      C.explicitModel)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    EuclideanYangMillsCanonicalRestrictedHamiltonianGapCertificate C B := by
  have h := euclidean_clustering_canonical_restricted_hamiltonian_exact_gap
    C A T E S F B hExactSpectrum
  exact
    { operatorSelfAdjoint := h.1
      operatorDomain :=
        canonical_vacuum_orthogonal_hamiltonian_domain C.explicitModel
      operatorDomainDense := h.2.1
      operatorClosed := h.2.2.1
      spectrumEqNonvacuum := B.restrictedSpectrum_eq_nonvacuum
      exactGapPositive := h.2.2.2.1
      spectrumLowerBound := h.2.2.2.2.1
      spectrumInfimum := h.2.2.2.2.2 }

end

end MathlibAnalytic
end MGAP4D
