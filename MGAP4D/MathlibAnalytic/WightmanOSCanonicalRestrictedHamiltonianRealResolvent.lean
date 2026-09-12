import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventSurjective
import MGAP4D.MathlibAnalytic.ExplicitWightmanOSExactGapPVMOpenSupportCore
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace LinearPMap

/-- Real parameters for which the shifted partially-defined operator is
algebraically bijective from its domain onto the Hilbert carrier. -/
def realBijectiveResolventSet
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E) : Set ℝ :=
  {lambda | Function.Bijective (A.realShift lambda)}

/-- The complementary real spectral obstruction set associated with bijectivity
of the shifted operator. -/
def realBijectiveSpectrum
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ.[ℝ] E) : Set ℝ :=
  (LinearPMap.realBijectiveResolventSet A)ᶜ

end LinearPMap

/-- A Rayleigh lower bound on the actual canonical restricted Hamiltonian makes
every real shift below the bound bijective. -/
theorem canonical_vacuum_orthogonal_realShift_bijective
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {mass lambda : ℝ} (hlambda : lambda < mass)
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        mass * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert)) :
    Function.Bijective
      (M.canonicalVacuumOrthogonalHamiltonian.realShift lambda) :=
  LinearPMap.realShift_bijective
    M.canonicalVacuumOrthogonalHamiltonian
    B.canonicalRestrictedSelfAdjoint hlambda hRayleigh

/-- The real shift below the Rayleigh threshold as an actual linear equivalence. -/
noncomputable def canonicalVacuumOrthogonalRealShiftLinearEquiv
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {mass lambda : ℝ} (hlambda : lambda < mass)
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        mass * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert)) :
    M.canonicalVacuumOrthogonalHamiltonian.domain ≃ₗ[ℝ]
      M.VacuumOrthogonalHilbert :=
  M.canonicalVacuumOrthogonalHamiltonian.realShiftLinearEquiv
    B.canonicalRestrictedSelfAdjoint hlambda hRayleigh

/-- The inverse real resolvent obeys the sharp coercive norm estimate. -/
theorem canonical_vacuum_orthogonal_realShift_inverse_norm_bound
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {mass lambda : ℝ} (hlambda : lambda < mass)
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        mass * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert))
    (y : M.VacuumOrthogonalHilbert) :
    (mass - lambda) *
        ‖((canonicalVacuumOrthogonalRealShiftLinearEquiv
          M B hlambda hRayleigh).symm y :
            M.VacuumOrthogonalHilbert)‖ ≤
      ‖y‖ :=
  M.canonicalVacuumOrthogonalHamiltonian.realShiftLinearEquiv_symm_norm_bound
    B.canonicalRestrictedSelfAdjoint hlambda hRayleigh y

/-- Every real parameter below the Rayleigh threshold belongs to the actual
bijective resolvent set of the canonical restricted Hamiltonian. -/
theorem canonical_vacuum_orthogonal_Iio_subset_realBijectiveResolventSet
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {mass : ℝ}
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        mass * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert)) :
    Set.Iio mass ⊆
      LinearPMap.realBijectiveResolventSet
        M.canonicalVacuumOrthogonalHamiltonian := by
  intro lambda hlambda
  exact canonical_vacuum_orthogonal_realShift_bijective
    M B hlambda hRayleigh

/-- Consequently the actual real spectral obstruction set has no point below the
Rayleigh threshold. -/
theorem canonical_vacuum_orthogonal_realBijectiveSpectrum_inter_Iio_eq_empty
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge M)
    {mass : ℝ}
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        mass * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert)) :
    LinearPMap.realBijectiveSpectrum
        M.canonicalVacuumOrthogonalHamiltonian ∩
      Set.Iio mass = ∅ := by
  ext lambda
  simp only [LinearPMap.realBijectiveSpectrum, Set.mem_inter_iff,
    Set.mem_compl_iff, Set.mem_Iio, Set.mem_empty_iff_false, iff_false]
  rintro ⟨hNotResolvent, hBelow⟩
  exact hNotResolvent
    (canonical_vacuum_orthogonal_Iio_subset_realBijectiveResolventSet
      M B hRayleigh hBelow)

/-- Complete exact-gap endpoint joining continuous PVM support with the actual
real resolvent exclusion of the canonical restricted Hamiltonian. -/
theorem explicit_wightman_os_exact_gap_pvm_support_and_real_resolvent
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hGap :
      HasHamiltonianMassGap M.hamiltonianEnergySpectrum exactGapValueReal)
    (hExactSpectrum :
      exactGapValueReal ∈ M.hamiltonianEnergySpectrum)
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert)) :
    IsLeast M.vacuumOrthogonalPVMOpenSupport exactGapValueReal ∧
      Set.Iio exactGapValueReal ⊆
        LinearPMap.realBijectiveResolventSet
          M.canonicalVacuumOrthogonalHamiltonian ∧
      LinearPMap.realBijectiveSpectrum
          M.canonicalVacuumOrthogonalHamiltonian ∩
        Set.Iio exactGapValueReal = ∅ := by
  exact ⟨
    B.exactGap_isLeast_pvmOpenSupport hGap hExactSpectrum,
    canonical_vacuum_orthogonal_Iio_subset_realBijectiveResolventSet
      M B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
        hRayleigh,
    canonical_vacuum_orthogonal_realBijectiveSpectrum_inter_Iio_eq_empty
      M B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
        hRayleigh⟩

end

end MathlibAnalytic
end MGAP4D
