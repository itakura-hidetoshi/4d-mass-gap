import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMSpectralSupport
import MGAP4D.MathlibAnalytic.EuclideanYangMillsFiniteVolumeClusteringLimit
import MGAP4D.MathlibAnalytic.EuclideanYangMillsNonAtomicPVMOpenSupportGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Legacy atomic specialization.

This route passes through singleton spectral weights and is therefore appropriate
only when the relevant non-vacuum spectrum is pure point.  It is not the main
continuous-spectrum Yang--Mills route. -/
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

/-- Legacy pure-point certificate constructor retained for the diagonal `ℓ²`
model and other explicitly atomic realizations. -/
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

/-- Main non-atomic route.

The lower spectral edge is obtained from positive mass in open neighborhoods,
so the Hilbert carrier may be infinite-dimensional and the spectrum may contain
a continuous component.  No assertion that `μ({E}) > 0` is used. -/
theorem euclidean_nonatomic_pvmOpenSupport_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (L : EuclideanYangMillsNonAtomicPVMOpenSupportBounds C)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge C.explicitModel) :
    IsSelfAdjoint C.explicitModel.canonicalVacuumOrthogonalHamiltonian ∧
      Dense ((C.explicitModel.canonicalVacuumOrthogonalHamiltonian.domain :
        Set C.explicitModel.VacuumOrthogonalHilbert)) ∧
      LinearPMap.IsClosed
        C.explicitModel.canonicalVacuumOrthogonalHamiltonian ∧
      C.explicitModel.vacuumOrthogonalPVMOpenSupport ⊆
        Set.Ici exactGapValueReal ∧
      B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal := by
  exact euclidean_nonatomic_canonical_hamiltonian_support_gap C L B

end

end MathlibAnalytic
end MGAP4D
