import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalHamiltonianGenerator
import MGAP4D.MathlibAnalytic.WightmanOSCanonicalRestrictedHamiltonianRealResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

/-- A lower support bound is exact when the support has points arbitrarily close
above the candidate threshold.  No point at the threshold itself is required. -/
theorem real_sInf_eq_of_subset_Ici_of_arbitrarily_close_above
    {s : Set ℝ} {m : ℝ}
    (hLower : s ⊆ Set.Ici m)
    (hClose : ∀ ε : ℝ, 0 < ε → ∃ E ∈ s, E < m + ε) :
    sInf s = m := by
  have hNonempty : s.Nonempty := by
    obtain ⟨E, hE, _⟩ := hClose 1 zero_lt_one
    exact ⟨E, hE⟩
  have hBdd : BddBelow s := by
    refine ⟨m, ?_⟩
    intro E hE
    exact hLower hE
  apply le_antisymm
  · by_contra hNot
    have hmInf : m < sInf s := lt_of_not_ge hNot
    let ε : ℝ := (sInf s - m) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨E, hE, hEclose⟩ := hClose ε hε
    have hInfLeE : sInf s ≤ E := csInf_le hBdd hE
    dsimp [ε] at hEclose
    linarith
  · exact le_csInf hNonempty fun E hE => hLower hE

/-- Continuous-spectrum-compatible endpoint.  A relativistic gap supplies the
support lower bound, while arbitrary approach from above identifies its infimum.
The same threshold controls the actual real resolvent of the canonical excitation
Hamiltonian. -/
abbrev ExplicitWightmanOSSharpPVMOpenSupportRealResolventProp
    (M : ExplicitWightmanOSReconstructedModel) : Prop :=
  M.vacuumOrthogonalPVMOpenSupport =
      M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) ∧
    0 < exactGapValueReal ∧
    M.vacuumOrthogonalPVMOpenSupport ⊆ Set.Ici exactGapValueReal ∧
    sInf M.vacuumOrthogonalPVMOpenSupport = exactGapValueReal ∧
    Set.Iio exactGapValueReal ⊆
      LinearPMap.realBijectiveResolventSet
        M.canonicalVacuumOrthogonalHamiltonian ∧
    LinearPMap.realBijectiveSpectrum
        M.canonicalVacuumOrthogonalHamiltonian ∩
      Set.Iio exactGapValueReal = ∅

/-- Replace exact-threshold membership by the support-sharpness condition
appropriate to continuous spectrum. -/
theorem explicit_wightman_os_relativistic_gap_sharp_pvm_support_real_resolvent
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hClose : ∀ ε : ℝ, 0 < ε →
      ∃ E ∈ M.vacuumOrthogonalPVMOpenSupport,
        E < exactGapValueReal + ε)
    (hRayleigh :
      ∀ x : M.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal * ‖(x : M.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ (M.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.VacuumOrthogonalHilbert)) :
    ExplicitWightmanOSSharpPVMOpenSupportRealResolventProp M := by
  have hGap : M.HasMassGap exactGapValueReal :=
    explicit_wightman_os_reconstruction_has_mass_gap M hRelGap
  have hSupportEq :
      M.vacuumOrthogonalPVMOpenSupport =
        M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) := by
    calc
      M.vacuumOrthogonalPVMOpenSupport = B.restrictedSpectrum :=
        B.pvmOpenSupport_eq_restrictedSpectrum
      _ = M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) :=
        B.restrictedSpectrum_eq_nonvacuum
  have hLower :
      M.vacuumOrthogonalPVMOpenSupport ⊆ Set.Ici exactGapValueReal := by
    rw [B.pvmOpenSupport_eq_restrictedSpectrum]
    exact vacuum_orthogonal_restrictedSpectrum_subset_Ici
      B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge.toExplicitWightmanOSVacuumOrthogonalSpectrumBridge
      hGap
  have hInfimum :
      sInf M.vacuumOrthogonalPVMOpenSupport = exactGapValueReal :=
    real_sInf_eq_of_subset_Ici_of_arbitrarily_close_above hLower hClose
  exact ⟨
    hSupportEq,
    hGap.1,
    hLower,
    hInfimum,
    canonical_vacuum_orthogonal_Iio_subset_realBijectiveResolventSet
      M B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
        hRayleigh,
    canonical_vacuum_orthogonal_realBijectiveSpectrum_inter_Iio_eq_empty
      M B.toExplicitWightmanOSCanonicalVacuumOrthogonalHamiltonianBridge
        hRayleigh⟩

/-- Generator-level endpoint without an eigenvalue or threshold-attainment input. -/
abbrev EuclideanYangMillsOSPhysicalGeneratorSharpPVMOpenSupportRealResolventProp
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) : Prop :=
  M.toExplicitModel.axioms.toLegacy = S.definitionBridge.spine.axioms ∧
    (∀ psi : M.observables.PhysicalHilbert,
      Tendsto (fun t : ℝ => T.operator t psi)
        (nhdsWithin 0 (Set.Ici 0)) (nhds psi)) ∧
    (∀ x : M.hamiltonian.domain,
      Tendsto
        (fun t : ℝ =>
          t⁻¹ •
            (T.operator t (x : M.observables.PhysicalHilbert) -
              (x : M.observables.PhysicalHilbert)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (-(M.hamiltonian x)))) ∧
    ExplicitWightmanOSSharpPVMOpenSupportRealResolventProp M.toExplicitModel

/-- The OS Hamiltonian generator, continuous PVM support, and actual real
resolvent share the same sharp lower edge even when that edge is not an
eigenvalue. -/
theorem euclidean_yang_mills_os_physical_generator_sharp_pvm_open_support_real_resolvent
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hClose : ∀ ε : ℝ, 0 < ε →
      ∃ E ∈ M.toExplicitModel.vacuumOrthogonalPVMOpenSupport,
        E < exactGapValueReal + ε)
    (hRayleigh :
      ∀ x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal *
            ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ
            (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.toExplicitModel.VacuumOrthogonalHilbert)) :
    EuclideanYangMillsOSPhysicalGeneratorSharpPVMOpenSupportRealResolventProp T := by
  have hOperator :=
    explicit_wightman_os_relativistic_gap_sharp_pvm_support_real_resolvent
      M.toExplicitModel B hRelGap hClose hRayleigh
  exact ⟨
    os_physical_reconstructed_model_uses_continuum_axioms M,
    G.stronglyContinuousAtZero,
    G.generatorLimit,
    hOperator⟩

end

end MathlibAnalytic
end MGAP4D
