import MGAP4D.MathlibAnalytic.EuclideanYangMillsVacuumOrthogonalGapBridge
import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMMeasureConstruction

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

end

end MathlibAnalytic
end MGAP4D
