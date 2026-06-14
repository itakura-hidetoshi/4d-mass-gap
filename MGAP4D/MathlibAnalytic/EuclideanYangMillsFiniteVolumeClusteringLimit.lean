import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMFiniteAdditivity
import Mathlib.Topology.Order.OrderClosed

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Finite-volume connected correlations converging pointwise to the continuum
correlations, with an exponential clustering estimate uniform in the
approximation index.

This package isolates the two concrete tasks needed on the Euclidean side:
construct the finite-volume correlations and prove a bound independent of the
volume/cutoff, then prove convergence to the continuum connected correlation. -/
structure EuclideanYangMillsFiniteVolumeClusteringApproximation
    (C : EuclideanYangMillsConnectedObservableCore) where
  finiteVolumeCorrelation :
    ℕ → C.explicitModel.NonVacuumEnergy → ℝ → ℝ
  pointwiseConvergence :
    ∀ (e : C.explicitModel.NonVacuumEnergy) (t : ℝ),
      Tendsto
        (fun n : ℕ => finiteVolumeCorrelation n e t)
        atTop
        (nhds (C.connectedCorrelation e t))
  uniformExponentialUpperBound :
    ∀ (n : ℕ) (e : C.explicitModel.NonVacuumEnergy)
      (t : ℝ), 0 ≤ t →
      finiteVolumeCorrelation n e t ≤
        C.decayConstant e * Real.exp (-exactGapValueReal * t)

/-- A uniform upper bound on every finite-volume approximation passes to the
continuum connected correlation. -/
theorem finite_volume_clustering_upper_bound_passes_to_limit
    {C : EuclideanYangMillsConnectedObservableCore}
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (e : C.explicitModel.NonVacuumEnergy) (t : ℝ) (ht : 0 ≤ t) :
    C.connectedCorrelation e t ≤
      C.decayConstant e * Real.exp (-exactGapValueReal * t) := by
  exact le_of_tendsto'
    (F.pointwiseConvergence e t)
    (fun n => F.uniformExponentialUpperBound n e t ht)

/-- The finite-volume approximation therefore constructs the continuum
exponential-clustering certificate. -/
def EuclideanYangMillsFiniteVolumeClusteringApproximation.toExponentialClustering
    {C : EuclideanYangMillsConnectedObservableCore}
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C) :
    EuclideanYangMillsExponentialClusteringEstimate C :=
  { upperBound := by
      intro e t ht
      exact finite_volume_clustering_upper_bound_passes_to_limit F e t ht }

/-- Hamiltonian mass gap once the PVM scalar measure and OS semigroup/spectral
identifications are combined with a uniform finite-volume clustering estimate. -/
theorem euclidean_finite_volume_clustering_mass_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C) :
    HasHamiltonianMassGap
      C.explicitModel.hamiltonianEnergySpectrum exactGapValueReal := by
  exact euclidean_quadratic_pvm_semigroup_clustering_mass_gap
    C A T E S F.toExponentialClustering

/-- Exact physical gap after passing the uniform finite-volume clustering estimate
to the continuum and assuming threshold spectral attainment. -/
theorem euclidean_finite_volume_clustering_exact_gap
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
  exact euclidean_quadratic_pvm_semigroup_clustering_exact_gap
    C A T E S F.toExponentialClustering hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
