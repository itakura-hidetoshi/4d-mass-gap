import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality
import MGAP4D.MathlibAnalytic.ExplicitWightmanOSPVMDetectedExactGapDefinitionBridge
import MGAP4D.MathlibAnalytic.ExplicitWightmanOSExactGapPVMOpenSupportCore
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- An orthogonal projection's quadratic form is its squared projected norm. -/
theorem OrthogonalProjectionValuedSetFunction.projection_norm_sq_eq_inner
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    (s : Set ℝ) (x : H) :
    ‖P.projection s x‖ ^ 2 = inner ℝ x (P.projection s x) := by
  calc
    ‖P.projection s x‖ ^ 2 =
        inner ℝ (P.projection s x) (P.projection s x) := by
      rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ x (P.projection s (P.projection s x)) :=
      P.selfAdjoint s x (P.projection s x)
    _ = inner ℝ x (P.projection s x) := by
      rw [P.idempotent]

/-- Finite disjoint additivity, self-adjointness, and idempotence force the ranges
of disjoint spectral projections to be orthogonal. -/
theorem OrthogonalProjectionValuedSetFunction.disjoint_projection_inner_eq_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {s t : Set ℝ} (hDisjoint : Disjoint s t) (x : H) :
    inner ℝ (P.projection s x) (P.projection t x) = 0 := by
  have hUnion := P.projection_norm_sq_eq_inner (s ∪ t) x
  have hLeft := P.projection_norm_sq_eq_inner s x
  have hRight := P.projection_norm_sq_eq_inner t x
  rw [P.disjoint_additive s t hDisjoint x] at hUnion
  rw [norm_add_sq_real, inner_add_right, ← hLeft, ← hRight] at hUnion
  nlinarith

/-- The product of two disjoint projections is zero.  Thus the standard PVM
multiplication law is already a theorem of the current finite-additive interface. -/
theorem OrthogonalProjectionValuedSetFunction.disjoint_projection_comp_apply_eq_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {s t : Set ℝ} (hDisjoint : Disjoint s t) (x : H) :
    P.projection s (P.projection t x) = 0 := by
  have hOrth :=
    P.disjoint_projection_inner_eq_zero hDisjoint (P.projection t x)
  rw [P.idempotent t x] at hOrth
  have hNorm := P.projection_norm_sq_eq_inner s (P.projection t x)
  have hNormSqZero : ‖P.projection s (P.projection t x)‖ ^ 2 = 0 := by
    calc
      ‖P.projection s (P.projection t x)‖ ^ 2 =
          inner ℝ (P.projection t x)
            (P.projection s (P.projection t x)) := hNorm
      _ = inner ℝ (P.projection s (P.projection t x))
            (P.projection t x) := real_inner_comm _ _
      _ = 0 := hOrth
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hNormSqZero)

/-- The former disjoint-composition input is generated from the existing PVM
fields and need not be supplied separately. -/
theorem OrthogonalProjectionValuedSetFunction.hasDisjointCompositionZero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    P.HasDisjointCompositionZero := by
  intro s t hDisjoint x
  exact P.disjoint_projection_comp_apply_eq_zero hDisjoint x

/-- Vacuum-orthogonality of every nonzero spectral projection is now automatic. -/
theorem explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal_of_finite_additivity
    (M : ExplicitWightmanOSReconstructedModel)
    {energy : ℝ} (hEnergy : energy ≠ 0) (psi : M.H) :
    M.spectralPVM.projection ({energy} : Set ℝ) psi ∈ M.vacuumOrthogonal :=
  explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal
    M M.spectralPVM.hasDisjointCompositionZero hEnergy psi

/-- Physical PVM detection at one nonzero energy supplies the concrete excitation
witness used by the vacuum-orthogonal spectrum bridge. -/
noncomputable def ExplicitWightmanOSSpectralPVMDetection.toNonzeroSpectralPVMWitness
    {M : ExplicitWightmanOSReconstructedModel}
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    {energy : ℝ} (hEnergy : energy ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : energy ≠ 0) :
    ExplicitWightmanOSNonzeroSpectralPVMWitness M := by
  classical
  let source := Classical.choose (D.detects energy hEnergy)
  exact
    { energy := energy
      energy_mem := hEnergy
      energy_ne_zero := hEnergyZero
      source := source
      projected_ne_zero := Classical.choose_spec (D.detects energy hEnergy) }

/-- The vacuum-orthogonal spectral bridge is generated from the current PVM laws
and one physically nonzero detected spectral value. -/
noncomputable def explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfDetection
    (M : ExplicitWightmanOSReconstructedModel)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    {energy : ℝ} (hEnergy : energy ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : energy ≠ 0) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    M M.spectralPVM.hasDisjointCompositionZero
    (D.toNonzeroSpectralPVMWitness hEnergy hEnergyZero)

/-- Add canonical restricted self-adjointness to the automatically generated
vacuum-orthogonal spectral bridge. -/
noncomputable def explicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridgeOfDetection
    (M : ExplicitWightmanOSReconstructedModel)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    {energy : ℝ} (hEnergy : energy ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : energy ≠ 0) :
    ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M :=
  { toExplicitWightmanOSVacuumOrthogonalSpectrumBridge :=
      explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfDetection
        M D hEnergy hEnergyZero
    canonicalRestrictedSelfAdjoint := hSelf }

/-- If pure PVM open support is identified with the physical non-vacuum spectrum,
the full continuous-spectrum bridge is generated without a separate PVM
multiplication hypothesis or excitation-sector nontriviality hypothesis. -/
noncomputable def explicitWightmanOSCanonicalPVMOpenSupportBridgeOfDetection
    (M : ExplicitWightmanOSReconstructedModel)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    {energy : ℝ} (hEnergy : energy ∈ M.hamiltonianEnergySpectrum)
    (hEnergyZero : energy ≠ 0)
    (hSupport :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) :
    ExplicitWightmanOSCanonicalPVMOpenSupportBridge M :=
  { toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge :=
      explicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridgeOfDetection
        M hSelf D hEnergy hEnergyZero
    pvmOpenSupport_eq_restrictedSpectrum := hSupport }

/-- Exact-gap specialization of the automatically generated pure-PVM support
bridge. -/
noncomputable def explicitWightmanOSExactGapPVMOpenSupportBridgeOfDetection
    (M : ExplicitWightmanOSReconstructedModel)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hSupport :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) :
    ExplicitWightmanOSCanonicalPVMOpenSupportBridge M :=
  explicitWightmanOSCanonicalPVMOpenSupportBridgeOfDetection
    M hSelf D hExactSpectrum (ne_of_gt hGap.1) hSupport

/-- The canonical restricted Hamiltonian and continuous-spectrum PVM support obey
the exact-gap theorem with disjoint PVM composition and excitation nontriviality
generated internally. -/
theorem explicit_wightman_os_exact_gap_pvm_open_support_of_detection
    (M : ExplicitWightmanOSReconstructedModel)
    (hSelf : IsSelfAdjoint M.canonicalVacuumOrthogonalHamiltonian)
    (D : ExplicitWightmanOSSpectralPVMDetection M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hSupport :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) :
    ExplicitWightmanOSExactGapPVMOpenSupportProp M
      (explicitWightmanOSExactGapPVMOpenSupportBridgeOfDetection
        M hSelf D hGap hExactSpectrum hSupport)
      hGap hExactSpectrum :=
  explicit_wightman_os_exact_gap_pvm_open_support
    M
    (explicitWightmanOSExactGapPVMOpenSupportBridgeOfDetection
      M hSelf D hGap hExactSpectrum hSupport)
    hGap hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
