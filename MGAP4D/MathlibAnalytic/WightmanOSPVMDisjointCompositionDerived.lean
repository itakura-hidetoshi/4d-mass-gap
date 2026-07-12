import MGAP4D.MathlibAnalytic.WightmanOSPVMVacuumOrthogonality
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite disjoint additivity, self-adjointness, and idempotence already force
orthogonality of disjoint spectral projection ranges.  Thus the disjoint
composition-zero law is not an independent PVM axiom for the repository's
projection-valued set-function interface. -/
theorem orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H) :
    P.HasDisjointCompositionZero := by
  intro s t hst x
  have hCross (z : H) :
      P.projection s (P.projection t z) +
          P.projection t (P.projection s z) = 0 := by
    have h := P.idempotent (s ∪ t) z
    rw [P.disjoint_additive s t hst (P.projection (s ∪ t) z),
      P.disjoint_additive s t hst z] at h
    simp only [map_add, P.idempotent] at h
    calc
      P.projection s (P.projection t z) +
          P.projection t (P.projection s z) =
          (P.projection s z + P.projection s (P.projection t z) +
              (P.projection t (P.projection s z) + P.projection t z)) -
            (P.projection s z + P.projection t z) := by abel
      _ = 0 := by rw [h, sub_self]
  have hPtPs (z : H) :
      P.projection t (P.projection s z) = 0 := by
    let q : H := P.projection t (P.projection s z)
    have hSum := hCross (P.projection s z)
    rw [P.idempotent s z] at hSum
    change P.projection s q + q = 0 at hSum
    have hInner :=
      congrArg (fun w : H => inner ℝ w (P.projection s z)) hSum
    simp only [inner_add_left, inner_zero_left] at hInner
    have hqInner :
        inner ℝ q (P.projection s z) = ‖q‖ ^ 2 := by
      calc
        inner ℝ q (P.projection s z) =
            inner ℝ (P.projection t q) (P.projection s z) := by
              rw [show P.projection t q = q by
                dsimp [q]
                exact P.idempotent t (P.projection s z)]
        _ = inner ℝ q (P.projection t (P.projection s z)) :=
          P.selfAdjoint t q (P.projection s z)
        _ = inner ℝ q q := by rfl
        _ = ‖q‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hFirst :
        inner ℝ (P.projection s q) (P.projection s z) = ‖q‖ ^ 2 := by
      calc
        inner ℝ (P.projection s q) (P.projection s z) =
            inner ℝ q (P.projection s (P.projection s z)) :=
          P.selfAdjoint s q (P.projection s z)
        _ = inner ℝ q (P.projection s z) := by
          rw [P.idempotent s z]
        _ = ‖q‖ ^ 2 := hqInner
    rw [hFirst, hqInner] at hInner
    have hqNormSq : ‖q‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖q‖]
    have hqZero : q = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hqNormSq)
    simpa [q] using hqZero
  have h := hCross x
  rw [hPtPs x, add_zero] at h
  exact h

/-- The reverse composition of two disjoint spectral projections also vanishes. -/
theorem orthogonalProjectionValuedSetFunction_disjoint_reverse_composition_zero
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (P : OrthogonalProjectionValuedSetFunction H)
    {s t : Set ℝ} (hst : Disjoint s t) (x : H) :
    P.projection t (P.projection s x) = 0 := by
  exact
    orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      P t s hst.symm x

/-- Every nonzero singleton spectral range lies in `Ω⊥` using only the PVM laws
already stored in the reconstructed model. -/
theorem explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal_canonical
    (M : ExplicitWightmanOSReconstructedModel)
    {E : ℝ} (hE : E ≠ 0) (ψ : M.H) :
    M.spectralPVM.projection ({E} : Set ℝ) ψ ∈ M.vacuumOrthogonal := by
  exact explicit_wightman_os_nonzero_pvm_range_mem_vacuumOrthogonal
    M
    (orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      M.spectralPVM)
    hE ψ

/-- The canonical PVM laws and one nonzero spectral vector construct the
vacuum-orthogonal spectrum bridge without a separate multiplication axiom. -/
def explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfCanonicalPVM
    (M : ExplicitWightmanOSReconstructedModel)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M) :
    ExplicitWightmanOSVacuumOrthogonalSpectrumBridge M :=
  explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfPVM
    M
    (orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      M.spectralPVM)
    W

/-- The reconstructed PVM laws turn a relativistic mass gap into the physical
spectral statement on `Ω⊥`, with no extra disjoint-composition input. -/
theorem explicit_wightman_os_canonical_pvm_vacuum_orthogonal_spectrum_gap
    (M : ExplicitWightmanOSReconstructedModel)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    0 < m ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆ Set.Ici m ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) = m := by
  exact explicit_wightman_os_pvm_vacuum_orthogonal_spectrum_gap
    M
    (orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      M.spectralPVM)
    W hRelGap hmSpectrum

/-- Exact-gap specialization with disjoint PVM orthogonality derived rather than
assumed. -/
theorem explicit_wightman_os_canonical_pvm_vacuum_orthogonal_exact_gap_positive
    (M : ExplicitWightmanOSReconstructedModel)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hExactSpectrum : exactGapValueReal ∈ M.hamiltonianEnergySpectrum) :
    0 < exactGapValueReal ∧
      (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) ⊆
        Set.Ici exactGapValueReal ∧
      sInf (M.hamiltonianEnergySpectrum \ ({0} : Set ℝ)) =
        exactGapValueReal := by
  exact explicit_wightman_os_pvm_vacuum_orthogonal_exact_gap_positive
    M
    (orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      M.spectralPVM)
    W hRelGap hExactSpectrum

/-- Full vacuum-orthogonal gap certificate from the canonical PVM laws and one
nonzero spectral witness. -/
def explicitWightmanOSCanonicalPVMVacuumOrthogonalGapCertificate
    (M : ExplicitWightmanOSReconstructedModel)
    (W : ExplicitWightmanOSNonzeroSpectralPVMWitness M)
    {m : ℝ}
    (hRelGap : HasRelativisticMassGap M.energyMomentumSpectrum m)
    (hmSpectrum : m ∈ M.hamiltonianEnergySpectrum) :
    ExplicitWightmanOSVacuumOrthogonalGapCertificate M
      (explicitWightmanOSVacuumOrthogonalSpectrumBridgeOfCanonicalPVM M W) m :=
  explicitWightmanOSPVMVacuumOrthogonalGapCertificate
    M
    (orthogonalProjectionValuedSetFunction_hasDisjointCompositionZero_of_projectionLaws
      M.spectralPVM)
    W hRelGap hmSpectrum

end

end MathlibAnalytic
end MGAP4D
