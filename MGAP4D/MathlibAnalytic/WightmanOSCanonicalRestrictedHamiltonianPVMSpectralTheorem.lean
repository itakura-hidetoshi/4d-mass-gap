import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianRealResolvent
import MGAP4D.MathlibAnalytic.WightmanOSPVMDisjointCompositionFromFiniteAdditivity
import MGAP4D.MathlibAnalytic.ExplicitWightmanOSScalarSupportToPVMOpenSupport

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
Package the actual spectral theorem for the canonical Hamiltonian on `Ω⊥` in a
form that generates the existing PVM and scalar support bridges.

The operator spectrum is no longer an unnamed set supplied directly to the
support bridge.  It is the real bijective spectrum of the actual partially
defined self-adjoint Hamiltonian, defined through failure of bijectivity of
`H|Ω⊥ - E I`.
-/

/-- Pointwise PVM spectral theorem for the actual canonical restricted
Hamiltonian.

The first field identifies its resolvent-defined real spectrum with the physical
non-vacuum energy spectrum.  The second field states the open-neighborhood PVM
characterization of membership, which remains valid for continuous spectrum and
does not require a singleton eigenprojection. -/
structure ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem
    (M : ExplicitWightmanOSReconstructedModel) where
  realSpectrum_eq_nonvacuum :
    LinearPMap.realBijectiveSpectrum
        M.canonicalVacuumOrthogonalHamiltonian =
      M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)
  mem_realSpectrum_iff_pvmOpenSupport :
    ∀ E : ℝ,
      E ∈ LinearPMap.realBijectiveSpectrum
          M.canonicalVacuumOrthogonalHamiltonian ↔
        ∃ ψ : M.VacuumOrthogonalHilbert,
          ∀ U : Set ℝ, E ∈ U → IsOpen U →
            M.spectralPVM.projection U (ψ : M.H) ≠ 0

/-- The pointwise spectral theorem identifies pure PVM open support with the
actual real operator spectrum of `H|Ω⊥`. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem.pvmOpenSupport_eq_realSpectrum
    {M : ExplicitWightmanOSReconstructedModel}
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M) :
    M.vacuumOrthogonalPVMOpenSupport =
      LinearPMap.realBijectiveSpectrum
        M.canonicalVacuumOrthogonalHamiltonian := by
  ext E
  simpa [ExplicitWightmanOSReconstructedModel.vacuumOrthogonalPVMOpenSupport]
    using (T.mem_realSpectrum_iff_pvmOpenSupport E).symm

/-- Hence the pure PVM open support is the physical non-vacuum Hamiltonian
spectrum, now as a theorem generated from the actual operator spectrum. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem.pvmOpenSupport_eq_nonvacuum
    {M : ExplicitWightmanOSReconstructedModel}
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M) :
    M.vacuumOrthogonalPVMOpenSupport =
      M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) := by
  calc
    M.vacuumOrthogonalPVMOpenSupport =
        LinearPMap.realBijectiveSpectrum
          M.canonicalVacuumOrthogonalHamiltonian :=
      T.pvmOpenSupport_eq_realSpectrum
    _ = M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) :=
      T.realSpectrum_eq_nonvacuum

/-- Canonical restricted self-adjointness, physical PVM detection, and the actual
spectral theorem generate the pure-PVM support bridge.  The PVM multiplication
law and excitation-sector nontriviality are supplied by the finite-additivity
theorems already present in the model. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem.toCanonicalPVMOpenSupportBridge
    {M : ExplicitWightmanOSReconstructedModel}
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    {energy : ℝ}
    (hEnergy : energy ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : energy ≠ 0) :
    ExplicitWightmanOSCanonicalPVMOpenSupportBridge M :=
  explicitWightmanOSCanonicalPVMOpenSupportBridgeOfDetection
    M hSelf D hEnergy hEnergyZero T.pvmOpenSupport_eq_nonvacuum

/-- Every full quadratic scalar realization receives its support bridge from the
same actual operator/PVM spectral theorem. -/
noncomputable def ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem.toCanonicalSpectralSupportBridge
    {M : ExplicitWightmanOSReconstructedModel}
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    {energy : ℝ}
    (hEnergy : energy ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : energy ≠ 0)
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M) :
    ExplicitWightmanOSCanonicalSpectralSupportBridge
      M F.toScalarSpectralRealization :=
  (T.toCanonicalPVMOpenSupportBridge
      hSelf D hEnergy hEnergyZero).toCanonicalSpectralSupportBridge F

/-- The union of all quadratic scalar supports is therefore the real spectrum of
the actual canonical restricted Hamiltonian. -/
theorem ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem.scalarSupport_eq_realSpectrum
    {M : ExplicitWightmanOSReconstructedModel}
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M)
    (F : ExplicitWightmanOSFullScalarSpectralMeasureRealization M) :
    M.canonicalVacuumOrthogonalSpectralSupport
        F.toScalarSpectralRealization =
      LinearPMap.realBijectiveSpectrum
        M.canonicalVacuumOrthogonalHamiltonian := by
  rw [full_scalar_vacuumOrthogonal_support_eq_pvmOpenSupport F]
  exact T.pvmOpenSupport_eq_realSpectrum

/-- Exact-gap endpoint generated from the actual canonical operator/PVM spectral
theorem.  No independent scalar-support or pure-PVM-support identification is
required. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_canonical_spectralTheorem
    (M : ExplicitWightmanOSReconstructedModel)
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp M
      (T.toCanonicalPVMOpenSupportBridge
        hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact explicit_wightman_os_exact_gap_pvm_open_support
    M
    (T.toCanonicalPVMOpenSupportBridge
      hSelf D hExactSpectrum (ne_of_gt hGap.1))
    hGap hExactSpectrum

/-- Quadratic PVM countable additivity now reaches the exact-gap theorem through
a scalar-support bridge generated by the same operator/PVM spectral theorem. -/
theorem explicit_wightman_os_quadratic_pvm_exact_gap_open_support_of_canonical_spectralTheorem
    (M : ExplicitWightmanOSReconstructedModel)
    (A : ExplicitWightmanOSQuadraticPVMCountableAdditivity M)
    (T : ExplicitWightmanOSCanonicalRestrictedPVMSpectralTheorem M)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp M
      (T.toCanonicalPVMOpenSupportBridge
        hSelf D hExactSpectrum (ne_of_gt hGap.1))
      hGap hExactSpectrum := by
  exact explicit_wightman_os_quadratic_pvm_exact_gap_open_support
    M A
    (T.toCanonicalSpectralSupportBridge
      hSelf D hExactSpectrum (ne_of_gt hGap.1)
      A.toFullScalarSpectralMeasureRealization)
    hGap hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
