import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalGeneratorSharpPVMOpenSupportRealResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

/-- Finite-volume transfer operators approximating the same completed OS physical
Hilbert space and time-translation semigroup used by the reconstructed
Hamiltonian.

The uniform infinitesimal decay slope is the analytic datum that will become the
Rayleigh lower bound of the actual generator. -/
structure EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : ℝ → ℝ
  slope_tendsto :
    Tendsto
      (fun t : ℝ => t⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  FiniteState : ℕ → Type
  [finiteNormedAddCommGroup : ∀ n, NormedAddCommGroup (FiniteState n)]
  [finiteInnerProductSpace : ∀ n, InnerProductSpace ℝ (FiniteState n)]
  finiteVacuum : (n : ℕ) → FiniteState n
  finiteOperator :
    (n : ℕ) → ℝ → FiniteState n →L[ℝ] FiniteState n
  approximate :
    (n : ℕ) → M.observables.PhysicalHilbert →L[ℝ] FiniteState n
  approximate_orthogonal :
    ∀ (n : ℕ) (ψ : M.observables.PhysicalHilbert),
      inner ℝ M.vacuum ψ = 0 →
        inner ℝ (approximate n ψ) (finiteVacuum n) = 0
  approximate_norm_tendsto :
    ∀ ψ : M.observables.PhysicalHilbert,
      Tendsto (fun n : ℕ => ‖approximate n ψ‖)
        atTop (nhds ‖ψ‖)
  evolved_norm_tendsto :
    ∀ (t : ℝ), 0 ≤ t → ∀ ψ : M.observables.PhysicalHilbert,
      Tendsto
        (fun n : ℕ => ‖finiteOperator n t (approximate n ψ)‖)
        atTop
        (nhds ‖T.operator t ψ‖)
  finite_decay :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → ∀ φ : FiniteState n,
      inner ℝ φ (finiteVacuum n) = 0 →
        ‖finiteOperator n t φ‖ ≤ decayFactor t * ‖φ‖

attribute [instance]
  EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer.finiteNormedAddCommGroup
  EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer.finiteInnerProductSpace

namespace EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer

/-- Scalar norm convergence transports the finite-volume vacuum-sector decay
estimate to the completed OS Hilbert space. -/
theorem continuum_decay
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (V : EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer T)
    (t : ℝ) (ht : 0 ≤ t)
    (ψ : M.observables.PhysicalHilbert)
    (hψ : inner ℝ M.vacuum ψ = 0) :
    ‖T.operator t ψ‖ ≤ V.decayFactor t * ‖ψ‖ := by
  apply le_of_tendsto_of_tendsto
    (V.evolved_norm_tendsto t ht ψ)
    (tendsto_const_nhds.mul (V.approximate_norm_tendsto ψ))
  exact Filter.Eventually.of_forall fun n =>
    V.finite_decay n t ht (V.approximate n ψ)
      (V.approximate_orthogonal n ψ hψ)

end EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer

/-- Positive-time Hamiltonian difference quotient associated with the reconstructed
OS semigroup. -/
def EuclideanYangMillsOSPhysicalTimeTranslation.hamiltonianDifferenceQuotient
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (ψ : M.observables.PhysicalHilbert)
    (t : ℝ) : M.observables.PhysicalHilbert :=
  t⁻¹ • (ψ - T.operator t ψ)

/-- The positive-time difference quotient converges to the reconstructed
Hamiltonian on its displayed domain. -/
theorem os_physical_hamiltonianDifferenceQuotient_tendsto
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (x : M.hamiltonian.domain) :
    Tendsto
      (fun t : ℝ =>
        T.hamiltonianDifferenceQuotient
          (x : M.observables.PhysicalHilbert) t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (M.hamiltonian x)) := by
  have hGenerator := (G.generatorLimit x).neg
  have hPointwise :
      (fun t : ℝ =>
        T.hamiltonianDifferenceQuotient
          (x : M.observables.PhysicalHilbert) t) =
      (fun t : ℝ =>
        -(t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert)))) := by
    funext t
    unfold EuclideanYangMillsOSPhysicalTimeTranslation.hamiltonianDifferenceQuotient
    calc
      t⁻¹ •
          ((x : M.observables.PhysicalHilbert) -
            T.operator t (x : M.observables.PhysicalHilbert)) =
        t⁻¹ •
          (-(T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert))) := by
          rw [neg_sub]
      _ =
        -(t⁻¹ •
          (T.operator t (x : M.observables.PhysicalHilbert) -
            (x : M.observables.PhysicalHilbert))) := by
          rw [smul_neg]
  rw [hPointwise]
  exact hGenerator

namespace EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer

/-- The finite-volume transfer gap gives the Rayleigh lower bound of the actual
Hamiltonian generator on every vacuum-orthogonal domain vector. -/
theorem hamiltonian_inner_ge_mass_mul_norm_sq
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (V : EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer T)
    (x : M.hamiltonian.domain)
    (hx :
      inner ℝ M.vacuum
        (x : M.observables.PhysicalHilbert) = 0) :
    V.mass * ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (M.hamiltonian x)
        (x : M.observables.PhysicalHilbert) := by
  have hHamiltonian :=
    os_physical_hamiltonianDifferenceQuotient_tendsto T G x
  have hSlope :
      Tendsto
        (fun t : ℝ =>
          (t⁻¹ * (1 - V.decayFactor t)) *
            ‖(x : M.observables.PhysicalHilbert)‖ ^ 2)
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (V.mass * ‖(x : M.observables.PhysicalHilbert)‖ ^ 2)) :=
    V.slope_tendsto.mul tendsto_const_nhds
  have hInner :
      Tendsto
        (fun t : ℝ =>
          inner ℝ
            (T.hamiltonianDifferenceQuotient
              (x : M.observables.PhysicalHilbert) t)
            (x : M.observables.PhysicalHilbert))
        (nhdsWithin 0 (Ioi 0))
        (nhds
          (inner ℝ (M.hamiltonian x)
            (x : M.observables.PhysicalHilbert))) :=
    hHamiltonian.inner tendsto_const_nhds
  apply le_of_tendsto_of_tendsto hSlope hInner
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htPos : 0 < t := ht
  have hInv : 0 ≤ t⁻¹ := inv_nonneg.mpr htPos.le
  have hDecay := V.continuum_decay T t htPos.le
    (x : M.observables.PhysicalHilbert) hx
  have hInnerBound :
      inner ℝ
          (T.operator t (x : M.observables.PhysicalHilbert))
          (x : M.observables.PhysicalHilbert) ≤
        V.decayFactor t *
          ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 := by
    calc
      inner ℝ
          (T.operator t (x : M.observables.PhysicalHilbert))
          (x : M.observables.PhysicalHilbert) ≤
        ‖T.operator t (x : M.observables.PhysicalHilbert)‖ *
          ‖(x : M.observables.PhysicalHilbert)‖ :=
        real_inner_le_norm _ _
      _ ≤
        (V.decayFactor t *
          ‖(x : M.observables.PhysicalHilbert)‖) *
            ‖(x : M.observables.PhysicalHilbert)‖ :=
        mul_le_mul_of_nonneg_right hDecay (norm_nonneg _)
      _ =
        V.decayFactor t *
          ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 := by ring
  have hSub :
      (1 - V.decayFactor t) *
          ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 ≤
        ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 -
          inner ℝ
            (T.operator t (x : M.observables.PhysicalHilbert))
            (x : M.observables.PhysicalHilbert) := by
    calc
      (1 - V.decayFactor t) *
          ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 =
        ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 -
          V.decayFactor t *
            ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 := by ring
      _ ≤
        ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 -
          inner ℝ
            (T.operator t (x : M.observables.PhysicalHilbert))
            (x : M.observables.PhysicalHilbert) :=
        sub_le_sub_left hInnerBound _
  calc
    (t⁻¹ * (1 - V.decayFactor t)) *
        ‖(x : M.observables.PhysicalHilbert)‖ ^ 2 =
      t⁻¹ *
        ((1 - V.decayFactor t) *
          ‖(x : M.observables.PhysicalHilbert)‖ ^ 2) := by ring
    _ ≤
      t⁻¹ *
        (‖(x : M.observables.PhysicalHilbert)‖ ^ 2 -
          inner ℝ
            (T.operator t (x : M.observables.PhysicalHilbert))
            (x : M.observables.PhysicalHilbert)) :=
      mul_le_mul_of_nonneg_left hSub hInv
    _ =
      inner ℝ
        (T.hamiltonianDifferenceQuotient
          (x : M.observables.PhysicalHilbert) t)
        (x : M.observables.PhysicalHilbert) := by
      simp only [
        EuclideanYangMillsOSPhysicalTimeTranslation.hamiltonianDifferenceQuotient,
        real_inner_smul_left, inner_sub_left,
        real_inner_self_eq_norm_sq]

/-- Restricting the generator inequality to `Ω⊥` supplies exactly the canonical
Rayleigh input used by the real-resolvent theorem. -/
theorem canonical_vacuumOrthogonalHamiltonian_rayleigh
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (V : EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer T)
    (x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain) :
    V.mass *
        ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
        (x : M.toExplicitModel.VacuumOrthogonalHilbert) := by
  let xAmbient : M.hamiltonian.domain :=
    M.toExplicitModel.vacuumOrthogonalAmbientDomainPoint x
  have hxOrthogonal :
      inner ℝ M.vacuum
        (xAmbient : M.observables.PhysicalHilbert) = 0 := by
    have hxVacuumFirst :
        inner ℝ M.vacuum
          (((x : M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.observables.PhysicalHilbert)) = 0 :=
      (explicit_wightman_os_mem_vacuumOrthogonal_iff
        M.toExplicitModel
        (((x : M.toExplicitModel.VacuumOrthogonalHilbert) :
          M.observables.PhysicalHilbert))).mp
        (x : M.toExplicitModel.VacuumOrthogonalHilbert).property
    simpa [xAmbient] using hxVacuumFirst
  have hAmbient :=
    V.hamiltonian_inner_ge_mass_mul_norm_sq
      T G xAmbient hxOrthogonal
  change
    V.mass *
        ‖(((x : M.toExplicitModel.VacuumOrthogonalHilbert) :
          M.observables.PhysicalHilbert))‖ ^ 2 ≤
      inner ℝ
        (((M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x :
          M.toExplicitModel.VacuumOrthogonalHilbert) :
            M.observables.PhysicalHilbert))
        (((x : M.toExplicitModel.VacuumOrthogonalHilbert) :
          M.observables.PhysicalHilbert))
  rw [canonical_vacuum_orthogonal_hamiltonian_apply]
  exact hAmbient

end EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer

/-- The finite-volume transfer approximation closes the former external
`hRayleigh` input in the sharp non-atomic support/resolvent endpoint. -/
theorem euclidean_yang_mills_os_finite_volume_transfer_sharp_support_real_resolvent
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (V : EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer T)
    (hMass : V.mass = exactGapValueReal)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hClose : ∀ ε : ℝ, 0 < ε →
      ∃ E ∈ M.toExplicitModel.vacuumOrthogonalPVMOpenSupport,
        E < exactGapValueReal + ε) :
    EuclideanYangMillsOSPhysicalGeneratorSharpPVMOpenSupportRealResolventProp T := by
  have hRayleigh :
      ∀ x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain,
        exactGapValueReal *
            ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
          inner ℝ
            (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
            (x : M.toExplicitModel.VacuumOrthogonalHilbert) := by
    intro x
    rw [← hMass]
    exact V.canonical_vacuumOrthogonalHamiltonian_rayleigh T G x
  exact
    euclidean_yang_mills_os_physical_generator_sharp_pvm_open_support_real_resolvent
      T G B hRelGap hClose hRayleigh

end

end MathlibAnalytic
end MGAP4D
