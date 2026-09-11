import MGAP4D.MathlibAnalytic.WightmanOSVacuumOrthogonalSpectrumGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Standard multiplication law for a projection-valued set function:
composition of the projections associated with two spectral sets is the
projection associated with their intersection. -/
def OrthogonalProjectionValuedSetFunction.HasCompositionIntersection
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) : Prop :=
  ∀ s t : Set ℝ, ∀ x : H,
    P.projection s (P.projection t x) = P.projection (s ∩ t) x

/-- Standard multiplicative law for a projection-valued measure on disjoint
Borel sets.  This is the disjoint-set consequence of the full intersection
composition law and remains available as the weakest assumption needed by the
vacuum-orthogonality argument below. -/
def OrthogonalProjectionValuedSetFunction.HasDisjointCompositionZero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) : Prop :=
  ∀ s t : Set ℝ, Disjoint s t → ∀ x : H,
    P.projection s (P.projection t x) = 0

/-- The standard intersection-composition law implies zero composition on
disjoint spectral sets. -/
theorem OrthogonalProjectionValuedSetFunction.hasDisjointCompositionZero_of_hasCompositionIntersection
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {P : OrthogonalProjectionValuedSetFunction H}
    (hComposition : P.HasCompositionIntersection) :
    P.HasDisjointCompositionZero := by
  intro s t hDisjoint x
  calc
    P.projection s (P.projection t x) = P.projection (s ∩ t) x :=
      hComposition s t x
    _ = P.projection ∅ x := by
      rw [Set.disjoint_iff_inter_eq_empty.mp hDisjoint]
    _ = 0 := P.empty_apply x

/-- Distinct singleton spectral sets are disjoint. -/
theorem singleton_zero_disjoint_singleton_of_ne_zero
    {E : ℝ} (hE : E ≠ 0) :
    Disjoint ({0} : Set ℝ) ({E} : Set ℝ) := by
  rw [Set.disjoint_left]
  intro x hx0 hxE
  have hx0' : x = 0 := by
    simpa using hx0
  have hxE' : x = E := by
    simpa using hxE
  apply hE
  calc
    E = x := hxE'.symm
    _ = 0 := hx0'

/-- Under the disjoint-product law, every vector in a nonzero singleton PVM
range lies in the physical vacuum-orthogonal sector `Ω⊥`. -/
theorem explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    {E : ℝ} (hE : E ≠ 0) (ψ : M.H) :
    M.spectralPVM.projection ({E} : Set ℝ) ψ ∈ M.vacuumOrthogonal := by
  rw [explicit_wightman_os_mem_vacuumOrthogonal_iff]
  have hDisjoint : Disjoint ({0} : Set ℝ) ({E} : Set ℝ) :=
    singleton_zero_disjoint_singleton_of_ne_zero hE
  have hCompositionZero :
      M.spectralPVM.projection ({0} : Set ℝ)
        (M.spectralPVM.projection ({E} : Set ℝ) ψ) = 0 :=
    hDisjointComposition ({0} : Set ℝ) ({E} : Set ℝ) hDisjoint ψ
  calc
    inner ℝ M.vacuum
        (M.spectralPVM.projection ({E} : Set ℝ) ψ) =
      inner ℝ
        (M.spectralPVM.projection ({0} : Set ℝ) M.vacuum)
        (M.spectralPVM.projection ({E} : Set ℝ) ψ) := by
          rw [M.vacuumSpectralProjection]
    _ = inner ℝ M.vacuum
        (M.spectralPVM.projection ({0} : Set ℝ)
          (M.spectralPVM.projection ({E} : Set ℝ) ψ)) :=
      M.spectralPVM.selfAdjoint ({0} : Set ℝ) M.vacuum
        (M.spectralPVM.projection ({E} : Set ℝ) ψ)
    _ = inner ℝ M.vacuum 0 := by
      rw [hCompositionZero]
    _ = 0 := by simp

/-- The full intersection-composition law gives the nonzero singleton range
orthogonality theorem directly. -/
theorem explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal_of_composition
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    {E : ℝ} (hE : E ≠ 0) (ψ : M.H) :
    M.spectralPVM.projection ({E} : Set ℝ) ψ ∈ M.vacuumOrthogonal := by
  exact explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal
    M
    (OrthogonalProjectionValuedSetFunction.hasDisjointCompositionZero_of_hasCompositionIntersection
      hComposition)
    hE ψ

/-- A concrete nonzero spectral-PVM vector.  This is the minimal nontriviality
input needed to show that `Ω⊥` contains an actual excitation vector rather than
only the zero vector. -/
structure ExplicitWightmanOSNonzeroSpectralPVMWitness
    (M : ExplicitWightmanOSReconstructedModel) where
  energy : ℝ
  energy_mem : energy ∈ M.hamiltonianEnergySpectrum
  energy_ne_zero : energy ≠ 0
  source : M.H
  projected_ne_zero :
    M.spectralPVM.projection ({energy} : Set ℝ) source ≠ 0

/-- Construct the vacuum-orthogonal spectrum bridge from the disjoint PVM
composition law and one nonzero spectral vector. -/
def explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M :=
  { restrictedSpectrum :=
      M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)
    restrictedSpectrum_eq_nonvacuum := rfl
    pvm_nonvacuum_range_orthogonal := by
      intro E hE ψ
      exact explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal
        M hDisjointComposition (by simpa using hE.2) ψ
    orthogonalSector_nontrivial := by
      have hOrthogonal :
          M.spectralPVM.projection ({W.energy} : Set ℝ) W.source ∈
            M.vacuumOrthogonal :=
        explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal
          M hDisjointComposition W.energy_ne_zero W.source
      exact ⟨
        ⟨M.spectralPVM.projection ({W.energy} : Set ℝ) W.source,
          hOrthogonal⟩,
        W.projected_ne_zero⟩ }

/-- Construct the vacuum-orthogonal spectrum bridge from the standard full PVM
intersection-composition law. -/
def explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVMComposition
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    M
    (OrthogonalProjectionValuedSetFunction.hasDisjointCompositionZero_of_hasCompositionIntersection
      hComposition)
    W

/-- The PVM disjoint-composition law turns a relativistic mass gap into the
physical spectral statement on `Ω⊥`. -/
theorem explicit_wightman_os_pvm_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    0 < m ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆ Set.Ici m ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = m := by
  let B := explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    M hDisjointComposition W
  have hPhysical :=
    explicit_wightman_os_vacuum_orthogonal_spectrum_gap
      M B hRelGap hmSpectrum
  rw [B.restrictedSpectrum_eq_nonvacuum] at hPhysical
  exact hPhysical

/-- The standard full PVM composition law turns a relativistic mass gap into
the physical spectral statement on `Ω⊥`. -/
theorem explicit_wightman_os_pvm_composition_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    0 < m ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆ Set.Ici m ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = m := by
  exact explicit_wightman_os_pvm_vacuum_orthogonal_spectrum_gap
    M
    (OrthogonalProjectionValuedSetFunction.hasDisjointCompositionZero_of_hasCompositionIntersection
      hComposition)
    W hRelGap hmSpectrum

/-- Exact-gap specialization obtained from the disjoint PVM law rather than a
primitive vacuum-orthogonality assumption. -/
theorem explicit_wightman_os_pvm_vacuum_orthogonal_exact_gap_positive
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact explicit_wightman_os_pvm_vacuum_orthogonal_spectrum_gap
    M hDisjointComposition W hRelGap hExactSpectrum

/-- Exact-gap specialization obtained directly from the standard full PVM
intersection-composition law. -/
theorem explicit_wightman_os_pvm_composition_vacuum_orthogonal_exact_gap_positive
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact explicit_wightman_os_pvm_composition_vacuum_orthogonal_spectrum_gap
    M hComposition W hRelGap hExactSpectrum

/-- Full theorem-level certificate constructed automatically from the disjoint
PVM law and a nonzero spectral-PVM witness. -/
def explicitWightmanOSPVMVacuumOrthogonalGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (hDisjointComposition :
      M.spectralPVM.HasDisjointCompositionZero)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSVacuumOrthogonalGapCertificate M
      (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
        M hDisjointComposition W) m :=
  explicitWightmanOSVacuumOrthogonalGapCertificate
    M
    (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
      M hDisjointComposition W)
    hRelGap hmSpectrum

/-- Full theorem-level certificate constructed from the standard full PVM
intersection-composition law and a nonzero spectral-PVM witness. -/
def explicitWightmanOSPVMCompositionVacuumOrthogonalGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (hComposition : M.spectralPVM.HasCompositionIntersection)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSVacuumOrthogonalGapCertificate M
      (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVMComposition
        M hComposition W) m :=
  explicitWightmanOSVacuumOrthogonalGapCertificate
    M
    (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVMComposition
      M hComposition W)
    hRelGap hmSpectrum

end

end MathlibAnalytic
end MGAP4D
