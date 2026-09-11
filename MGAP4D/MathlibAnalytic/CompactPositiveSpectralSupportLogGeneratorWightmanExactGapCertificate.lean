import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorWightmanIntertwining
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianPointSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace lp LinearPMap Topology BigOperators

noncomputable section

/-- Terminal spectral certificate joining the actual one-step transfer-support
logarithmic generator to the reconstructed Wightman Hamiltonian on `Ω⊥`.

The two genuinely different identification layers remain explicit:

* `operatorIntertwining` identifies the actual partially-defined operators by a
  norm-preserving real-linear equivalence with exact domain transport;
* `wightmanPointSpectrum` identifies the actual canonical restricted-Hamiltonian
  point spectrum with the PVM non-vacuum spectral set.

Once those two bridges are supplied, the mass-gap value itself and its
attainment are no longer separate transfer-side assumptions. -/
structure PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ) where
  operatorIntertwining :
    PeriodicHypercubicEvenSpecialUnitaryTransferLogGeneratorWightmanIntertwining
      H N hN beta hbeta M
  wightmanPointSpectrum : ExplicitWightmanOSCanonicalPointSpectrumBridge M
  massGap : M.HasMassGap m
  gapMem : m ∈ M.hamiltonianEnergySpectrum

/-- The transfer logarithmic-generator point-energy set is exactly the Wightman
PVM non-vacuum spectral set.  This equality is derived by composing the
operator-level and PVM-level bridges; it is not an additional certificate
field. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_pointEnergySet_eq_restrictedSpectrum
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      C.wightmanPointSpectrum.restrictedSpectrum := by
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta =
      M.canonicalVacuumOrthogonalPointSpectrum :=
        periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
          H N hN beta hbeta M C.operatorIntertwining
    _ = C.wightmanPointSpectrum.restrictedSpectrum :=
      C.wightmanPointSpectrum.pointSpectrum_eq_restrictedSpectrum

/-- The actual Wightman gap is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_positive
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m) :
    0 < m :=
  C.massGap.1

/-- The intrinsic lower edge of the actual one-step transfer logarithmic
spectrum is exactly the Wightman mass-gap value. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_logEnergyInf_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta = m := by
  rw [periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_logEnergyInf_eq_wightmanPointSpectrum_inf
    H N hN beta hbeta M C.operatorIntertwining]
  exact canonical_vacuum_orthogonal_pointSpectrum_sInf_eq
    C.wightmanPointSpectrum C.massGap C.gapMem

/-- Every admissible-resolvent asymptotic effective-energy variational floor is
exactly the Wightman mass-gap value. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_effectiveEnergyLimitSet_inf_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m)
    (hSupport : ∃ v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta, v ≠ 0)
    (lambda : ℝ)
    (hlambda : |lambda| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) :
    sInf
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportEffectiveEnergyLimitSet
          H N hN beta hbeta lambda) = m := by
  rw [periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_effectiveEnergyLimitSet_inf_eq_wightmanPointSpectrum_inf
    H N hN beta hbeta M C.operatorIntertwining hSupport lambda hlambda]
  exact canonical_vacuum_orthogonal_pointSpectrum_sInf_eq
    C.wightmanPointSpectrum C.massGap C.gapMem

/-- The finite-volume coercive decay scale stays a rigorous lower bound for the
actual Wightman mass gap.  No equality with the finite-volume scale is asserted. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_ge_two_mul_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m)
    (hSupport : ∃ v :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta, v ≠ 0) :
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤ m := by
  calc
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta ≤
      sInf M.canonicalVacuumOrthogonalPointSpectrum :=
        periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_wightmanPointSpectrum_inf_ge_two_mul_finiteVolumeDecayRate
          H N hN beta hbeta M C.operatorIntertwining hSupport
    _ = m := canonical_vacuum_orthogonal_pointSpectrum_sInf_eq
      C.wightmanPointSpectrum C.massGap C.gapMem

/-- The mass-gap value is attained by a genuine nonzero eigenvector of the
actual canonical Wightman Hamiltonian on `Ω⊥`. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_exists_wightman_eigenvector
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m) :
    ∃ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
      (x : M.VacuumOrthogonalHilbert) ≠ 0 ∧
        M.canonicalVacuumOrthogonalHamiltonian x =
          m • (x : M.VacuumOrthogonalHilbert) := by
  exact canonical_vacuum_orthogonal_exact_gap_eigenvector
    C.wightmanPointSpectrum C.massGap.1 C.gapMem

/-- The same attained Wightman mass-gap eigenvalue is transported back to a
genuine nonzero eigenvector of the actual one-step transfer-support logarithmic
generator.  This is the operator-level realization of the mass-gap value on the
transfer side. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_exists_transferLogGenerator_eigenvector
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) (m : ℝ)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
      H N hN beta hbeta M m) :
    ∃ x :
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
        H N hN beta hbeta).domain,
      (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
        H N hN beta hbeta) ≠ 0 ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGenerator
          H N hN beta hbeta x =
        m • (x : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
          H N hN beta hbeta) := by
  have hmPoint :
      m ∈ M.canonicalVacuumOrthogonalPointSpectrum := by
    rw [C.wightmanPointSpectrum.pointSpectrum_eq_restrictedSpectrum,
      C.wightmanPointSpectrum.restrictedSpectrum_eq_nonvacuum]
    exact ⟨C.gapMem, by simpa using ne_of_gt C.massGap.1⟩
  have hsets :=
    periodicHypercubicEvenSpecialUnitaryTransferLogGenerator_pointSpectrum_eq_wightman
      H N hN beta hbeta M C.operatorIntertwining
  have hmTransfer :
      m ∈ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogGeneratorPointEnergySet
        H N hN beta hbeta := by
    rw [hsets]
    exact hmPoint
  exact hmTransfer

/-- Exact-gap-value specialization. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryTransferWightmanExactGapCertificate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel) :=
  PeriodicHypercubicEvenSpecialUnitaryTransferWightmanMassGapCertificate
    H N hN beta hbeta M exactGapValueReal

/-- Under the exact-gap terminal certificate, the intrinsic transfer floor is
the repository's canonical exact gap value. -/
theorem periodicHypercubicEvenSpecialUnitaryTransferWightmanExactGap_logEnergyInf_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (M : ExplicitWightmanOSReconstructedModel)
    (C : PeriodicHypercubicEvenSpecialUnitaryTransferWightmanExactGapCertificate
      H N hN beta hbeta M) :
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportLogEnergyInf
        H N hN beta hbeta = exactGapValueReal :=
  periodicHypercubicEvenSpecialUnitaryTransferWightmanMassGap_logEnergyInf_eq
    H N hN beta hbeta M exactGapValueReal C

end

end MathlibAnalytic
end MGAP4D
