import MGAP4D.MathlibAnalytic.EuclideanYangMillsCanonicalRestrictedHamiltonianGap
import MGAP4D.MathlibAnalytic.WightmanOSScalarSpectralMeasureRealization
import Mathlib.MeasureTheory.Measure.Support

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-- The spectral support seen by all vectors in the physical non-vacuum Hilbert
sector.  Unlike point spectrum, this includes continuous spectral support. -/
def ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalSpectralSupport
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M) : Set ℝ :=
  ⋃ ψ : M.VacuumOrthogonalHilbert,
    (R.scalarMeasure (ψ : M.H)).support

/-- Membership in the physical scalar-measure support means that at least one
vacuum-orthogonal vector has the energy in the support of its scalar measure. -/
theorem mem_canonical_vacuum_orthogonal_spectralSupport_iff
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M)
    (E : ℝ) :
    E ∈ M.canonicalVacuumOrthogonalSpectralSupport R ↔
      ∃ ψ : M.VacuumOrthogonalHilbert,
        E ∈ (R.scalarMeasure (ψ : M.H)).support := by
  simp [ExplicitWightmanOSReconstructedModel.canonicalVacuumOrthogonalSpectralSupport]

/-- Identification input between the support of the vector-indexed scalar
spectral measures and the physical non-vacuum spectral set.  This is the
continuous-spectrum analogue of the optional point-spectrum bridge. -/
structure ExplicitWightmanOSCanonicalSpectralSupportBridge
    (M : ExplicitWightmanOSReconstructedModel)
    (R : ExplicitWightmanOSScalarSpectralMeasureRealization M) extends
      ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M where
  spectralSupport_eq_restrictedSpectrum :
    M.canonicalVacuumOrthogonalSpectralSupport R = restrictedSpectrum

/-- Vacuum energy is absent from the scalar-measure support on `Ω⊥`. -/
theorem canonical_vacuum_orthogonal_spectralSupport_zero_not_mem
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R) :
    0 ∉ M.canonicalVacuumOrthogonalSpectralSupport R := by
  rw [B.spectralSupport_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_zero_not_mem
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge

/-- Every energy in the full scalar-measure support lies above a proven
Hamiltonian mass gap. -/
theorem canonical_vacuum_orthogonal_spectralSupport_lower_bound
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    {m : ℝ} (hGap : M.HasMassGap m) :
    M.canonicalVacuumOrthogonalSpectralSupport R ⊆ Set.Ici m := by
  rw [B.spectralSupport_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_subset_Ici
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    hGap

/-- If the lower threshold belongs to the Hamiltonian energy spectrum, it is the
infimum of the full scalar-measure support. -/
theorem canonical_vacuum_orthogonal_spectralSupport_sInf_eq
    {M : ExplicitWightmanOSReconstructedModel}
    {R : ExplicitWightmanOSScalarSpectralMeasureRealization M}
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge M R)
    {m : ℝ} (hGap : M.HasMassGap m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    sInf (M.canonicalVacuumOrthogonalSpectralSupport R) = m := by
  rw [B.spectralSupport_eq_restrictedSpectrum]
  exact vacuum_orthogonal_restrictedSpectrum_sInf_eq
    B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
    hGap hmSpectrum

/-- Euclidean finite-volume clustering yields a positive lower bound on the full
continuous spectral support of the actual vacuum-sector Hamiltonian. -/
theorem euclidean_clustering_canonical_spectralSupport_lower_bound
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      C.explicitModel A.toScalarSpectralRealization) :
    0 < exactGapValueReal ∧
      C.explicitModel.canonicalVacuumOrthogonalSpectralSupport
        A.toScalarSpectralRealization ⊆ Set.Ici exactGapValueReal := by
  have hGap : C.explicitModel.HasMassGap exactGapValueReal :=
    euclidean_finite_volume_clustering_mass_gap C A T E S F
  exact ⟨hGap.1,
    canonical_vacuum_orthogonal_spectralSupport_lower_bound B hGap⟩

/-- Exact support-level physical gap, without assuming the lower threshold is an
eigenvalue. -/
theorem euclidean_clustering_canonical_spectralSupport_exact_gap
    (C : EuclideanYangMillsConnectedObservableCore)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity C.explicitModel)
    (T : ExplicitWightmanOSEuclideanTimeSemigroup C.explicitModel)
    (E : EuclideanYangMillsConnectedCorrelationSemigroupIdentification C T)
    (S : ExplicitWightmanOSSpectralSemigroupLaplaceFormula
      C.explicitModel A.toScalarSpectralRealization T)
    (F : EuclideanYangMillsFiniteVolumeClusteringApproximation C)
    (B : ExplicitWightmanOSCanonicalSpectralSupportBridge
      C.explicitModel A.toScalarSpectralRealization)
    (hExactSpectrum :
      exactGapValueReal ∈ C.explicitModel.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      C.explicitModel.canonicalVacuumOrthogonalSpectralSupport
        A.toScalarSpectralRealization ⊆ Set.Ici exactGapValueReal ∧
      sInf (C.explicitModel.canonicalVacuumOrthogonalSpectralSupport
        A.toScalarSpectralRealization) = exactGapValueReal := by
  have hGap : C.explicitModel.HasMassGap exactGapValueReal :=
    euclidean_finite_volume_clustering_mass_gap C A T E S F
  exact ⟨hGap.1,
    canonical_vacuum_orthogonal_spectralSupport_lower_bound B hGap,
    canonical_vacuum_orthogonal_spectralSupport_sInf_eq
      B hGap hExactSpectrum⟩

end

end MathlibAnalytic
end MGAP4D
