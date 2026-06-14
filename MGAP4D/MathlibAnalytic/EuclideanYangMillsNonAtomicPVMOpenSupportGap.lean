import MGAP4D.MathlibAnalytic.WightmanOSConnectedCorrelationOpenSupportGap
import MGAP4D.MathlibAnalytic.WightmanOSQuadraticPVMSpectralSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The non-atomic analytic bridge for the Yang--Mills physical sector.

Its support is the PVM open support on `Ω⊥`.  Local Laplace lower bounds come
from positive spectral mass in neighborhoods, not from atoms at singleton
energies. -/
structure EuclideanYangMillsNonAtomicPVMOpenSupportBounds
    (C : EuclideanYangMillsConnectedObservableCore) where
  bounds :
    ExplicitWightmanOSConnectedCorrelationOpenSupportBounds exactGapValueReal
  spectralSupport_eq_pvmOpenSupport :
    bounds.spectralSupport =
      C.explicitModel.vacuumOrthogonalPVMOpenSupport

/-- The non-atomic correlation argument gives the physical PVM support gap. -/
theorem euclidean_nonatomic_pvmOpenSupport_lower_bound
    (C : EuclideanYangMillsConnectedObservableCore)
    (L : EuclideanYangMillsNonAtomicPVMOpenSupportBounds C) :
    C.explicitModel.vacuumOrthogonalPVMOpenSupport ⊆
      Set.Ici exactGapValueReal := by
  rw [← L.spectralSupport_eq_pvmOpenSupport]
  exact connected_correlation_open_support_subset_Ici L.bounds

/-- Join the non-atomic support argument to the actual canonical Hamiltonian on
`Ω⊥`.  No singleton spectral mass and no gap eigenvector are required. -/
theorem euclidean_nonatomic_canonical_hamiltonian_support_gap
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
  have hSupport :
      C.explicitModel.vacuumOrthogonalPVMOpenSupport ⊆
        Set.Ici exactGapValueReal :=
    euclidean_nonatomic_pvmOpenSupport_lower_bound C L
  have hRestricted : B.restrictedSpectrum ⊆ Set.Ici exactGapValueReal := by
    rw [← B.pvmOpenSupport_eq_restrictedSpectrum]
    exact hSupport
  exact ⟨B.canonicalRestrictedSelfAdjoint,
    canonical_vacuum_orthogonal_hamiltonian_dense_domain
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge,
    canonical_vacuum_orthogonal_hamiltonian_isClosed
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge,
    hSupport, hRestricted⟩

end

end MathlibAnalytic
end MGAP4D
