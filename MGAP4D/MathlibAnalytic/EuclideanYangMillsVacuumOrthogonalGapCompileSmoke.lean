import MGAP4D.MathlibAnalytic.EuclideanYangMillsVacuumOrthogonalGapBridge
import MGAP4D.MathlibAnalytic.EuclideanYangMillsFiniteVolumeClusteringLimit
import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalRestrictedHamiltonian

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Integration theorem forcing the original dependency chain

`typed OS/Wightman model → reconstructed Hilbert space → Hamiltonian spectrum →
PVM vacuum orthogonality → Euclidean construction spine → exact positive gap`

to elaborate in one Lean target. -/
theorem euclidean_yang_mills_vacuum_orthogonal_gap_compile_smoke
    (B : EuclideanYangMillsVacuumOrthogonalGapBridge) :
    0 < exactGapValueReal ∧
      (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (B.explicitModel.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact euclidean_yang_mills_nonvacuum_hamiltonian_exact_gap B

/-- Integration theorem forcing the independent analytic route

`continuum Euclidean measure → measure-defined connected correlations →
countably additive scalar PVM measures → OS semigroup Laplace representation →
exponential clustering → physical Ω⊥ exact gap`

to elaborate in one target. -/
theorem euclidean_yang_mills_countably_additive_gap_compile_smoke
    (C : EuclideanYangMillsConnectedObservableCore)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure C.explicitModel)
    (L : EuclideanYangMillsOSLaplaceSemigroupIdentification
      C P.toScalarSpectralRealization)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble L.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble L.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_countably_additive_pvm_semigroup_clustering_exact_gap
    C P L X hExactSpectrum

/-- Integration theorem forcing the fully factored OS route

`Euclidean correlation → exp(-tH) matrix coefficient → scalar spectral
Laplace transform → singleton spectral atom → exponential clustering → gap`. -/
theorem euclidean_yang_mills_semigroup_factorization_compile_smoke
    (C : EuclideanYangMillsConnectedObservableCore)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel P.toScalarSpectralRealization T)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    let L :=
      euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients E S
    0 < exactGapValueReal ∧
      ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble L.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble L.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_semigroup_spectral_formula_clustering_exact_gap
    C P T E S X hExactSpectrum

/-- Integration theorem forcing actual construction of the scalar measures from
one quadratic PVM countable-additivity law. -/
theorem euclidean_yang_mills_quadratic_pvm_measure_compile_smoke
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    let L :=
      euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients E S
    0 < exactGapValueReal ∧
      ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble L.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble L.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_quadratic_pvm_semigroup_clustering_exact_gap
    C A T E S X hExactSpectrum

/-- The finite quadratic measure laws are already consequences of the weak PVM
interface plus disjoint-composition zero. -/
theorem euclidean_yang_mills_quadratic_pvm_finite_laws_compile_smoke
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasDisjointCompositionZero) :
    (∀ ψ : M.H,
      M.quadraticPVMWeight ψ ∅ MeasurableSet.empty = 0) ∧
    (∀ (ψ : M.H) {s t : Set ℝ}
      (hs : MeasurableSet s) (ht : MeasurableSet t),
      Disjoint s t →
        M.quadraticPVMWeight ψ (s ∪ t) (hs.union ht) =
          M.quadraticPVMWeight ψ s hs +
            M.quadraticPVMWeight ψ t ht) := by
  exact explicit_wightman_os_quadratic_pvm_finite_measure_laws
    M hComposition

/-- Integration theorem forcing the uniform finite-volume clustering bound to
pass to the continuum before the physical gap theorem is invoked. -/
theorem euclidean_yang_mills_finite_volume_clustering_compile_smoke
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    let L :=
      euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients E S
    0 < exactGapValueReal ∧
      ((C.assemble L.toOSSpectralLaplace
        F.toExponentialClustering).vacuumOrthogonalSpectrum
          ((C.assemble L.toOSSpectralLaplace
            F.toExponentialClustering).exactEnergy
              hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble L.toOSSpectralLaplace
          F.toExponentialClustering).vacuumOrthogonalSpectrum
            ((C.assemble L.toOSSpectralLaplace
              F.toExponentialClustering).exactEnergy
                hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_finite_volume_clustering_exact_gap
    C A T E S F hExactSpectrum

/-- The physical vacuum-orthogonal carrier is complete by the reusable instance
registered on the orthogonal-complement carrier. -/
theorem explicit_wightman_os_vacuum_orthogonal_complete_compile_smoke
    (M : ExplicitWightmanOSReconstructedModel) :
    CompleteSpace M.VacuumOrthogonalHilbert := by
  infer_instance

/-- Integration theorem forcing the actual partially-defined restriction
`H|Ω⊥` to elaborate with its intersection domain and self-adjointness surface. -/
theorem explicit_wightman_os_restricted_hamiltonian_compile_smoke
    {M : ExplicitWightmanOSReconstructedModel}
    (B : ExplicitWightmanOSVacuumOrthogonalRestrictedHamiltonianBridge M) :
    IsSelfAdjoint B.operator ∧
      B.operator.domain = M.vacuumOrthogonalHamiltonianDomain := by
  exact ⟨vacuum_orthogonal_restrictedHamiltonian_isSelfAdjoint B, rfl⟩

/-- The restricted operator agrees with the ambient Hamiltonian after inclusion
of both its domain point and its value into the physical Hilbert space. -/
theorem explicit_wightman_os_restricted_hamiltonian_action_compile_smoke
    {M : ExplicitWightmanOSReconstructedModel}
    (I : ExplicitWightmanOSVacuumOrthogonalHamiltonianInvariant M)
    (x : I.restrictedHamiltonian.domain) :
    ((I.restrictedHamiltonian x : M.VacuumOrthogonalHilbert) : M.H) =
      M.hamiltonian (M.vacuumOrthogonalAmbientDomainPoint x) := by
  exact vacuum_orthogonal_restrictedHamiltonian_apply I x

end

end MathlibAnalytic
end MGAP4D
