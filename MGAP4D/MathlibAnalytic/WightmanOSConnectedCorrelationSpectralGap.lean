import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A typed connected-correlation decay certificate for a reconstructed
OS/Wightman model.

For every non-vacuum spectral energy `E`, `spectralLaplaceLowerBound` records the
positive spectral contribution `w(E) exp(-E t)` beneath the connected Euclidean
correlation.  The global correlation is bounded above by `C exp(-Δ t)`.  The
final field isolates the elementary exponential-separation step: if `E < Δ`,
then at some nonnegative Euclidean time the spectral lower contribution exceeds
the claimed global decay upper bound. -/
structure ExplicitWightmanOSConnectedCorrelationDecayCertificate
    (M : ExplicitWightmanOSReconstructedModel) (Δ : ℝ) where
  correlation : ℝ → ℝ
  decayConstant : ℝ
  decayConstant_nonneg : 0 ≤ decayConstant
  spectralWeight : ℝ → ℝ
  gapPositive : 0 < Δ
  spectralWeight_pos :
    ∀ {E : ℝ},
      E ∈ M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) →
        0 < spectralWeight E
  spectralLaplaceLowerBound :
    ∀ {E : ℝ},
      E ∈ M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) →
        ∀ t : ℝ, 0 ≤ t →
          spectralWeight E * Real.exp (-E * t) ≤ correlation t
  connectedCorrelationExponentialUpperBound :
    ∀ t : ℝ, 0 ≤ t →
      correlation t ≤ decayConstant * Real.exp (-Δ * t)
  subgapExponentialSeparation :
    ∀ {E : ℝ},
      E ∈ M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) →
        E < Δ →
          ∃ t : ℝ,
            0 ≤ t ∧
              decayConstant * Real.exp (-Δ * t) <
                spectralWeight E * Real.exp (-E * t)

/-- Connected-correlation exponential decay excludes every non-vacuum energy
strictly below `Δ`. -/
theorem connected_correlation_decay_nonvacuum_spectrum_subset_Ici
    {M : ExplicitWightmanOSReconstructedModel} {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationDecayCertificate M Δ) :
    M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) ⊆ Set.Ici Δ := by
  intro E hE
  show Δ ≤ E
  by_contra hNot
  have hSubgap : E < Δ := lt_of_not_ge hNot
  obtain ⟨t, ht, hSeparation⟩ :=
    D.subgapExponentialSeparation hE hSubgap
  have hLower := D.spectralLaplaceLowerBound hE t ht
  have hUpper := D.connectedCorrelationExponentialUpperBound t ht
  linarith

/-- If the normalized vacuum contributes the zero spectral value, connected
correlation decay produces a Hamiltonian mass gap without using a primitive
`firstExcitation_pos` field. -/
theorem connected_correlation_decay_hasHamiltonianMassGap
    {M : ExplicitWightmanOSReconstructedModel} {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationDecayCertificate M Δ)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum) :
    HasHamiltonianMassGap M.hamiltonianEnergySpectrum Δ := by
  refine ⟨D.gapPositive, hVacuumSpectrum, ?_⟩
  intro E hE hE0
  have hNonvacuum :
      E ∈ M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) :=
    ⟨hE, by simpa using hE0⟩
  exact connected_correlation_decay_nonvacuum_spectrum_subset_Ici D hNonvacuum

/-- When the decay threshold is itself a spectral point, it is the infimum of the
non-vacuum Hamiltonian spectrum. -/
theorem connected_correlation_decay_sInf_nonvacuum_eq
    {M : ExplicitWightmanOSReconstructedModel} {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationDecayCertificate M Δ)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum)
    (hThresholdSpectrum : Δ ∈ M.hamiltonianEnergySpectrum) :
    sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = Δ := by
  exact hasHamiltonianMassGap_sInf_nonvacuum_eq
    (connected_correlation_decay_hasHamiltonianMassGap D hVacuumSpectrum)
    hThresholdSpectrum

/-- Connected-correlation decay transfers directly to the physical
vacuum-orthogonal spectrum bridge. -/
theorem connected_correlation_decay_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (B : ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M)
    {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationDecayCertificate M Δ)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum)
    (hThresholdSpectrum : Δ ∈ M.hamiltonianEnergySpectrum) :
    0 < Δ ∧
      B.restrictedSpectrum ⊆ Set.Ici Δ ∧
      sInf B.restrictedSpectrum = Δ := by
  have hGap : M.HasMassGap Δ :=
    connected_correlation_decay_hasHamiltonianMassGap D hVacuumSpectrum
  exact ⟨D.gapPositive,
    vacuum_orthogonal_restrictedSpectrum_subset_Ici B hGap,
    vacuum_orthogonal_restrictedSpectrum_sInf_eq B hGap hThresholdSpectrum⟩

/-- Under the standard PVM disjoint-product law and one nonzero spectral vector,
connected-correlation decay gives the complete physical `Ω⊥` spectral gap. -/
theorem connected_correlation_decay_pvm_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationDecayCertificate M Δ)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum)
    (hThresholdSpectrum : Δ ∈ M.hamiltonianEnergySpectrum) :
    0 < Δ ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆ Set.Ici Δ ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = Δ := by
  let B := explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    M hDisjointComposition W
  have hPhysical :=
    connected_correlation_decay_vacuum_orthogonal_spectrum_gap
      M B D hVacuumSpectrum hThresholdSpectrum
  rw [B.restrictedSpectrum_eq_nonvacuum] at hPhysical
  exact hPhysical

/-- Exact-gap specialization of the connected-correlation route. -/
theorem connected_correlation_decay_pvm_exact_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    (D : ExplicitWightmanOSConnectedCorrelationDecayCertificate
      M exactGapValueReal)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact connected_correlation_decay_pvm_vacuum_orthogonal_spectrum_gap
    M hDisjointComposition W D hVacuumSpectrum hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
