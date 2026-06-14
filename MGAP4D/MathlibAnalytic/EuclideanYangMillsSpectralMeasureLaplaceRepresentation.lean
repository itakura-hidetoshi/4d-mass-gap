import MGAP4D.MathlibAnalytic.EuclideanYangMillsConnectedCorrelationAnalyticInputs
import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Positive scalar spectral measures for the connected-observable core.

For the source vector attached to each non-vacuum energy `e`, the Euclidean
connected correlation is represented as the Laplace transform of a genuine
Mathlib measure on the Hamiltonian energy line.  The singleton atom at `e` is
identified with the canonical scalar PVM mass
`‖P({e}) ψₑ‖²`. -/
structure EuclideanYangMillsPositiveSpectralMeasureRepresentation
    (C : EuclideanYangMillsConnectedObservableCore) where
  spectralMeasure :
    C.explicitModel.NonVacuumEnergy → Measure ℝ
  laplaceIntegrable :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      Integrable
        (fun λ : ℝ => Real.exp (-λ * t))
        (spectralMeasure e)
  correlation_eq_laplaceIntegral :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ), 0 ≤ t →
      C.connectedCorrelation e t =
        ∫ λ : ℝ, Real.exp (-λ * t) ∂spectralMeasure e
  singletonMass_eq_squaredProjectionNorm :
    ∀ e : C.explicitModel.NonVacuumEnergy,
      (spectralMeasure e).real ({(e : ℝ)} : Set ℝ) =
        ‖C.explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
          (C.sourceVector e)‖ ^ 2

/-- The spectral measure has strictly positive mass at the selected non-vacuum
energy because the corresponding singleton-PVM projection is nonzero. -/
theorem positive_spectral_measure_singleton_mass_pos
    {C : EuclideanYangMillsConnectedObservableCore}
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (e : C.explicitModel.NonVacuumEnergy) :
    0 < (S.spectralMeasure e).real ({(e : ℝ)} : Set ℝ) := by
  rw [S.singletonMass_eq_squaredProjectionNorm e]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (C.projectedSource_ne_zero e))

/-- The integral over the singleton spectral atom is exactly its squared-PVM
weight multiplied by the Euclidean semigroup factor. -/
theorem positive_spectral_measure_singleton_laplace_integral
    {C : EuclideanYangMillsConnectedObservableCore}
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (e : C.explicitModel.NonVacuumEnergy) (t : ℝ) :
    (∫ λ : ℝ in ({(e : ℝ)} : Set ℝ),
      Real.exp (-λ * t) ∂S.spectralMeasure e) =
      ‖C.explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
        (C.sourceVector e)‖ ^ 2 * Real.exp (-(e : ℝ) * t) := by
  rw [MeasureTheory.integral_singleton]
  rw [S.singletonMass_eq_squaredProjectionNorm e]
  simp [smul_eq_mul]

/-- Positivity of the Laplace integrand makes the singleton spectral contribution
no larger than the full scalar spectral integral. -/
theorem positive_spectral_measure_singleton_le_full_laplace
    {C : EuclideanYangMillsConnectedObservableCore}
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (e : C.explicitModel.NonVacuumEnergy) (t : ℝ) (ht : 0 ≤ t) :
    (∫ λ : ℝ in ({(e : ℝ)} : Set ℝ),
      Real.exp (-λ * t) ∂S.spectralMeasure e) ≤
      ∫ λ : ℝ, Real.exp (-λ * t) ∂S.spectralMeasure e := by
  exact MeasureTheory.setIntegral_le_integral
    (S.laplaceIntegrable e t ht)
    (Filter.Eventually.of_forall fun λ => (Real.exp_pos (-λ * t)).le)

/-- A positive scalar spectral-measure representation automatically supplies the
OS spectral Laplace lower-bound certificate. -/
def EuclideanYangMillsPositiveSpectralMeasureRepresentation.toOSSpectralLaplace
    {C : EuclideanYangMillsConnectedObservableCore}
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C) :
    EuclideanYangMillsOSSpectralLaplaceRepresentation C :=
  { lowerBound := by
      intro e t ht
      calc
        ‖C.explicitModel.spectralPVM.projection ({(e : ℝ)} : Set ℝ)
            (C.sourceVector e)‖ ^ 2 * Real.exp (-(e : ℝ) * t) =
            ∫ λ : ℝ in ({(e : ℝ)} : Set ℝ),
              Real.exp (-λ * t) ∂S.spectralMeasure e :=
          (positive_spectral_measure_singleton_laplace_integral
            S e t).symm
        _ ≤ ∫ λ : ℝ, Real.exp (-λ * t) ∂S.spectralMeasure e :=
          positive_spectral_measure_singleton_le_full_laplace S e t ht
        _ = C.connectedCorrelation e t :=
          (S.correlation_eq_laplaceIntegral e t ht).symm }

/-- Once the positive spectral-measure representation and exponential clustering
estimate are supplied, the Hamiltonian mass gap follows.  The lower-bound half
is no longer an independent assumption. -/
theorem euclidean_spectral_measure_and_clustering_hasHamiltonianMassGap
    (C : EuclideanYangMillsConnectedObservableCore)
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_connected_correlation_analytic_inputs_hasHamiltonianMassGap
    C S.toOSSpectralLaplace X

/-- Exact physical gap from the scalar spectral measure, exponential clustering,
and spectral attainment of the threshold. -/
theorem euclidean_spectral_measure_and_clustering_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (S : EuclideanYangMillsPositiveSpectralMeasureRepresentation C)
    (X : EuclideanYangMillsExponentialClusteringEstimate C)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      ((C.assemble S.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
        ((C.assemble S.toOSSpectralLaplace X).exactEnergy
          hExactSpectrum)).restrictedSpectrum ⊆
        Set.Ici exactGapValueReal ∧
      sInf
        ((C.assemble S.toOSSpectralLaplace X).vacuumOrthogonalSpectrum
          ((C.assemble S.toOSSpectralLaplace X).exactEnergy
            hExactSpectrum)).restrictedSpectrum =
        exactGapValueReal := by
  exact euclidean_connected_correlation_analytic_inputs_exact_gap
    C S.toOSSpectralLaplace X hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
