import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality
import Mathlib.Analysis.SpecialFunctions.Exp

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A positive slower exponential eventually dominates any nonnegative multiple
of a strictly faster exponential.  This is the elementary asymptotic mechanism
behind the implication

`connected Euclidean correlation decays as exp(-Δ t)`
`→ no positive spectral contribution can occur at E < Δ`. -/
theorem exists_subgap_exponential_separation
    {a C E Δ : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C) (hSubgap : E < Δ) :
    ∃ t : ℝ,
      0 ≤ t ∧
        C * Real.exp (-Δ * t) < a * Real.exp (-E * t) := by
  by_cases hC0 : C = 0
  · refine ⟨0, le_rfl, ?_⟩
    simpa [hC0] using ha
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    have hRatioPos : 0 < a / C := div_pos ha hCpos
    have hEventually :
        ∀ᶠ x : ℝ in Filter.atTop, Real.exp (-x) < a / C :=
      Real.tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const hRatioPos
    obtain ⟨x, hxSmall, hxNonneg⟩ :=
      (hEventually.and (Filter.eventually_ge_atTop (0 : ℝ))).exists
    let d : ℝ := Δ - E
    have hd : 0 < d := by
      dsimp [d]
      linarith
    let t : ℝ := x / d
    have ht : 0 ≤ t := by
      exact div_nonneg hxNonneg hd.le
    have hCexp : C * Real.exp (-x) < a := by
      have hxSmall' : Real.exp (-x) * C < a :=
        (lt_div_iff₀ hCpos).mp hxSmall
      simpa [mul_comm] using hxSmall'
    have hdt : d * t = x := by
      dsimp [t]
      field_simp [ne_of_gt hd]
    have hExponent : -Δ * t = (-E * t) + (-x) := by
      rw [← hdt]
      dsimp [d]
      ring
    refine ⟨t, ht, ?_⟩
    rw [hExponent, Real.exp_add]
    calc
      C * (Real.exp (-E * t) * Real.exp (-x)) =
          (C * Real.exp (-x)) * Real.exp (-E * t) := by ring
      _ < a * Real.exp (-E * t) :=
        mul_lt_mul_of_pos_right hCexp (Real.exp_pos _)

/-- A typed connected-correlation decay certificate for a reconstructed
OS/Wightman model.

For every non-vacuum spectral energy `E`, `spectralLaplaceLowerBound` records the
positive spectral contribution `w(E) exp(-E t)` beneath the connected Euclidean
correlation.  The global correlation is bounded above by `C exp(-Δ t)`. -/
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

/-- The user-facing Laplace-bound package.  Unlike the lower-level certificate,
it does not ask for a separately supplied exponential-separation witness: that
witness is derived automatically from positivity of the spectral weight and
`Real.exp (-x) → 0`. -/
structure ExplicitWightmanOSConnectedCorrelationLaplaceBounds
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

/-- Automatically discharge the subgap exponential-separation field. -/
def ExplicitWightmanOSConnectedCorrelationLaplaceBounds.toDecayCertificate
    {M : ExplicitWightmanOSReconstructedModel} {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationLaplaceBounds M Δ) :
    ExplicitWightmanOSConnectedCorrelationDecayCertificate M Δ :=
  { correlation := D.correlation
    decayConstant := D.decayConstant
    decayConstant_nonneg := D.decayConstant_nonneg
    spectralWeight := D.spectralWeight
    gapPositive := D.gapPositive
    spectralWeight_pos := D.spectralWeight_pos
    spectralLaplaceLowerBound := D.spectralLaplaceLowerBound
    connectedCorrelationExponentialUpperBound :=
      D.connectedCorrelationExponentialUpperBound
    subgapExponentialSeparation := by
      intro E hE hSubgap
      exact exists_subgap_exponential_separation
        (D.spectralWeight_pos hE) D.decayConstant_nonneg hSubgap }

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

/-- The same spectral exclusion theorem from the simpler Laplace-bound package. -/
theorem connected_correlation_laplace_bounds_nonvacuum_spectrum_subset_Ici
    {M : ExplicitWightmanOSReconstructedModel} {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationLaplaceBounds M Δ) :
    M.hamiltonianEnergySpectrum \ ({0} : Set ℝ) ⊆ Set.Ici Δ := by
  exact connected_correlation_decay_nonvacuum_spectrum_subset_Ici
    D.toDecayCertificate

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

/-- Hamiltonian mass gap from the automatically completed Laplace-bound package. -/
theorem connected_correlation_laplace_bounds_hasHamiltonianMassGap
    {M : ExplicitWightmanOSReconstructedModel} {Δ : ℝ}
    (D : ExplicitWightmanOSConnectedCorrelationLaplaceBounds M Δ)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum) :
    HasHamiltonianMassGap M.hamiltonianEnergySpectrum Δ := by
  exact connected_correlation_decay_hasHamiltonianMassGap
    D.toDecayCertificate hVacuumSpectrum

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

/-- Exact-gap specialization from the simpler Laplace-bound package. -/
theorem connected_correlation_laplace_bounds_pvm_exact_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    (D : ExplicitWightmanOSConnectedCorrelationLaplaceBounds
      M exactGapValueReal)
    (hVacuumSpectrum : 0 ∈ M.hamiltonianEnergySpectrum)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact connected_correlation_decay_pvm_exact_gap
    M hDisjointComposition W D.toDecayCertificate
      hVacuumSpectrum hExactSpectrum

end

end MathlibAnalytic
end MGAP4D
