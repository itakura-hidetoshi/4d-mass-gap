import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHilbertReconstructedModel
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianRealResolvent

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The explicit Wightman model exported from the continuum OS Hilbert
reconstruction retains the reconstructed Hamiltonian definitionally. -/
@[simp] theorem euclidean_yang_mills_os_physical_explicitModel_hamiltonian
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.hamiltonian = M.hamiltonian :=
  rfl

/-- The exported explicit model retains the reconstructed energy spectrum
without a transport layer. -/
@[simp] theorem euclidean_yang_mills_os_physical_explicitModel_energySpectrum
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S) :
    M.toExplicitModel.hamiltonianEnergySpectrum =
      M.hamiltonianEnergySpectrum :=
  rfl

/-- Compact endpoint joining the continuum measure axioms, the OS physical
Hilbert completion, continuous PVM support, and the actual real resolvent of the
canonical excitation Hamiltonian. -/
abbrev EuclideanYangMillsOSPhysicalExactGapRealResolventProp
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hRayleigh :
      ∀ x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal *
            ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ
            (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.toExplicitModel.VacuumOrthogonalHilbert)) : Prop :=
  M.toExplicitModel.axioms.toLegacy = S.definitionBridge.spine.axioms ∧
    IsLeast M.toExplicitModel.vacuumOrthogonalPVMOpenSupport
      exactGapValueReal ∧
    Set.Iio exactGapValueReal ⊆
      LinearPMap.realBijectiveResolventSet
        M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian ∧
    LinearPMap.realBijectiveSpectrum
        M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian ∩
      Set.Iio exactGapValueReal = ∅

/-- The continuum OS physical reconstruction reaches the exact continuous
spectral-support threshold and the real resolvent exclusion on its actual
canonical excitation Hamiltonian.

The Hamiltonian mass-gap input is not supplied separately: it is generated from
the reconstructed joint energy-momentum spectrum by the existing relativistic
gap theorem. -/
theorem euclidean_yang_mills_os_physical_exact_gap_real_resolvent
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    (M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hRayleigh :
      ∀ x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal *
            ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ
            (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.toExplicitModel.VacuumOrthogonalHilbert)) :
    EuclideanYangMillsOSPhysicalExactGapRealResolventProp
      M B hRelGap hExactSpectrum hRayleigh := by
  have hGap :
      HasHamiltonianMassGap
        M.toExplicitModel.hamiltonianEnergySpectrum exactGapValueReal :=
    os_physical_reconstructed_model_has_mass_gap M hRelGap
  have hOperator :=
    explicit_wightman_os_exact_gap_pvm_support_and_real_resolvent
      M.toExplicitModel B hGap hExactSpectrum hRayleigh
  exact ⟨
    os_physical_reconstructed_model_uses_continuum_axioms M,
    hOperator.1,
    hOperator.2.1,
    hOperator.2.2⟩

end

end MathlibAnalytic
end MGAP4D
