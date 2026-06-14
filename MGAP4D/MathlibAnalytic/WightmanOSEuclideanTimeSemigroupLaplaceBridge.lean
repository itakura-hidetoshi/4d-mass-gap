import MGAP4D.MathlibAnalytic.WightmanOSCountablyAdditivePVMScalarMeasure

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Bounded Euclidean-time semigroup reconstructed on the physical Hilbert space.

The present interface records the semigroup laws on nonnegative times, the
identity at time zero, vacuum preservation, and contractivity.  It is the bounded
`exp(-tH)` layer associated with the possibly unbounded Hamiltonian generator. -/
structure ExplicitWightmanOSEuclideanTimeSemigroup
    (M : ExplicitWightmanOSReconstructedModel) where
  operator : ℝ → M.H →L[ℝ] M.H
  zero_apply : ∀ ψ : M.H, operator 0 ψ = ψ
  add_apply :
    ∀ (s t : ℝ), 0 ≤ s → 0 ≤ t → ∀ ψ : M.H,
      operator (s + t) ψ = operator s (operator t ψ)
  vacuum_fixed :
    ∀ t : ℝ, 0 ≤ t → operator t M.vacuum = M.vacuum
  contraction :
    ∀ (t : ℝ), 0 ≤ t → ∀ ψ : M.H, ‖operator t ψ‖ ≤ ‖ψ‖

/-- The Euclidean measure correlation is the Hilbert-space matrix coefficient of
the reconstructed Euclidean-time semigroup. -/
structure EuclideanYangMillsConnectedCorrelationSemigroupIdentification
    (C : EuclideanYangMillsConnectedObservableCore)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel) where
  correlation_eq_matrixCoefficient :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      C.connectedCorrelation e t =
        inner ℝ (C.sourceVector e) (T.operator t (C.sourceVector e))

/-- Spectral-theorem evaluation of the Euclidean semigroup matrix coefficient.
For each Hilbert vector, the scalar spectral measure of the Hamiltonian turns
`exp(-tH)` into the Laplace kernel `exp(-λt)`. -/
structure ExplicitWightmanOSSpectralSemigroupLaplaceFormula
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup M) where
  laplaceIntegrable :
    ∀ (ψ : M.H) (t : ℝ), 0 ≤ t →
      Integrable
        (fun λ : ℝ => Real.exp (-λ * t))
        (R.scalarMeasure ψ)
  matrixCoefficient_eq_laplaceIntegral :
    ∀ (ψ : M.H) (t : ℝ), 0 ≤ t →
      inner ℝ ψ (T.operator t ψ) =
        ∫ λ : ℝ, Real.exp (-λ * t) ∂R.scalarMeasure ψ

/-- The correlation-to-semigroup identification and the spectral theorem formula
compose to the OS Laplace-semigroup identification used downstream. -/
def euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients
    {C : EuclideanYangMillsConnectedObservableCore}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization C.explicitModel}
    {T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel}
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel R T) :
    EuclideanYangMillsOSLaplaceSemigroupIdentification C R :=
  { laplaceIntegrable := by
      intro e t ht
      exact S.laplaceIntegrable (C.sourceVector e) t ht
    correlation_eq_laplaceIntegral := by
      intro e t ht
      calc
        C.connectedCorrelation e t =
            inner ℝ (C.sourceVector e)
              (T.operator t (C.sourceVector e)) :=
          E.correlation_eq_matrixCoefficient e t ht
        _ = ∫ λ : ℝ, Real.exp (-λ * t)
              ∂R.scalarMeasure (C.sourceVector e) :=
          S.matrixCoefficient_eq_laplaceIntegral
            (C.sourceVector e) t ht }

/-- Hamiltonian mass gap from the countably additive PVM scalar measures,
Euclidean-time semigroup reconstruction, the two matrix-coefficient
identifications, and exponential clustering. -/
theorem euclidean_semigroup_spectral_formula_clustering_mass_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (P : ExplicitWightmanOSCountablyAdditivePVMScalarMeasure C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel P.toScalarSpectralRealization T)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  let L := euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients
    E S
  exact euclidean_countably_additive_pvm_semigroup_clustering_mass_gap
    C P L X

/-- Exact physical gap through the fully factored semigroup/spectral route. -/
theorem euclidean_semigroup_spectral_formula_clustering_exact_gap
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
  dsimp
  let L := euclideanYangMillsOSLaplaceSemigroupIdentificationOfMatrixCoefficients
    E S
  exact euclidean_countably_additive_pvm_semigroup_clustering_exact_gap
    C P L X hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
