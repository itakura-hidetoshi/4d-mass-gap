import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMSpectralSupport
import MGAP4D.MathlibAnalytic.EuclideanYangMillsFiniteVolumeClusteringLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Uniform finite-volume clustering gives the exact lower edge of the full PVM
open support after continuum passage. -/
theorem euclidean_finite_volume_pvmOpenSupport_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge C.explicitModel)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      C.explicitModel.vacuumOrthogonalPVMOpenSupport ⊆
        Set.Ici exactGapValueReal ∧
      sInf C.explicitModel.vacuumOrthogonalPVMOpenSupport =
        exactGapValueReal := by
  exact euclidean_clustering_pvmOpenSupport_exact_gap
    C A T E S F.toExponentialClustering B hExactSpectrum

/-- End-to-end constructor from finite-volume Euclidean correlations to the
actual canonical vacuum-sector Hamiltonian and its full continuous spectral
support. -/
def euclideanFiniteVolumeCanonicalPVMOpenSupportGapCertificate
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge C.explicitModel)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    EuclideanYangMillsCanonicalPVMOpenSupportGapCertificate C B :=
  euclideanYangMillsCanonicalPVMOpenSupportGapCertificate
    C A T E S F.toExponentialClustering B hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
