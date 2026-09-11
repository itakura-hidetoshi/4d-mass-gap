import MGAP4D.MathlibAnalytic.EuclideanYangMillsOSPhysicalFiniteVolumeTransferRayleigh

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Topology

/-- Common-carrier finite-volume approximation of the reconstructed OS physical
semigroup.

Each finite Hilbert carrier is embedded isometrically into the completed physical
Hilbert space.  Vector convergence of the embedded states and evolved states
produces the scalar norm convergence required by the finite-volume Rayleigh
transfer theorem. -/
structure EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : ℝ → ℝ
  slope_tendsto :
    Tendsto
      (fun t : ℝ => t⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds mass)
  FiniteState : ℕ → Type
  [finiteNormedAddCommGroup : ∀ n, NormedAddCommGroup (FiniteState n)]
  [finiteInnerProductSpace : ∀ n, InnerProductSpace ℝ (FiniteState n)]
  finiteVacuum : (n : ℕ) → FiniteState n
  finiteOperator :
    (n : ℕ) → ℝ → FiniteState n →L[ℝ] FiniteState n
  approximate :
    (n : ℕ) → M.observables.PhysicalHilbert →L[ℝ] FiniteState n
  embed :
    (n : ℕ) → FiniteState n →L[ℝ] M.observables.PhysicalHilbert
  embed_norm :
    ∀ (n : ℕ) (φ : FiniteState n), ‖embed n φ‖ = ‖φ‖
  approximate_orthogonal :
    ∀ (n : ℕ) (ψ : M.observables.PhysicalHilbert),
      inner ℝ M.vacuum ψ = 0 →
        inner ℝ (approximate n ψ) (finiteVacuum n) = 0
  approximate_tendsto :
    ∀ ψ : M.observables.PhysicalHilbert,
      Tendsto
        (fun n : ℕ => embed n (approximate n ψ))
        atTop
        (nhds ψ)
  evolved_tendsto :
    ∀ (t : ℝ), 0 ≤ t → ∀ ψ : M.observables.PhysicalHilbert,
      Tendsto
        (fun n : ℕ => embed n (finiteOperator n t (approximate n ψ)))
        atTop
        (nhds (T.operator t ψ))
  finite_decay :
    ∀ (n : ℕ) (t : ℝ), 0 ≤ t → ∀ φ : FiniteState n,
      inner ℝ φ (finiteVacuum n) = 0 →
        ‖finiteOperator n t φ‖ ≤ decayFactor t * ‖φ‖

attribute [instance]
  EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer.finiteNormedAddCommGroup
  EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer.finiteInnerProductSpace

namespace EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer

/-- Isometric vector convergence constructs the exact finite-volume transfer
package used by the canonical Rayleigh theorem. -/
noncomputable def toFiniteVolumeVacuumGapTransfer
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    {T : EuclideanYangMillsOSPhysicalTimeTranslation M}
    (E : EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer T) :
    EuclideanYangMillsOSPhysicalFiniteVolumeVacuumGapTransfer T where
  mass := E.mass
  mass_pos := E.mass_pos
  decayFactor := E.decayFactor
  slope_tendsto := E.slope_tendsto
  FiniteState := E.FiniteState
  finiteNormedAddCommGroup := E.finiteNormedAddCommGroup
  finiteInnerProductSpace := E.finiteInnerProductSpace
  finiteVacuum := E.finiteVacuum
  finiteOperator := E.finiteOperator
  approximate := E.approximate
  approximate_orthogonal := E.approximate_orthogonal
  approximate_norm_tendsto := by
    intro ψ
    have hNorm := (E.approximate_tendsto ψ).norm
    simpa only [E.embed_norm] using hNorm
  evolved_norm_tendsto := by
    intro t ht ψ
    have hNorm := (E.evolved_tendsto t ht ψ).norm
    simpa only [E.embed_norm] using hNorm
  finite_decay := E.finite_decay

/-- The embedded approximation directly generates the canonical Rayleigh lower
bound on the actual vacuum-orthogonal Hamiltonian. -/
theorem canonical_vacuumOrthogonalHamiltonian_rayleigh
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (E : EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer T)
    (x : M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian.domain) :
    E.mass *
        ‖(x : M.toExplicitModel.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (M.toExplicitModel.canonicalVacuumOrthogonalHamiltonian x)
        (x : M.toExplicitModel.VacuumOrthogonalHilbert) :=
  E.toFiniteVolumeVacuumGapTransfer
    |>.canonical_vacuumOrthogonalHamiltonian_rayleigh T G x

/-- The common-carrier embedded finite-volume construction reaches the sharp
continuous-support real-resolvent endpoint without a separately postulated
Rayleigh inequality. -/
theorem sharp_support_real_resolvent
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {M : EuclideanYangMillsOSPhysicalHilbertReconstructedModel S}
    (T : EuclideanYangMillsOSPhysicalTimeTranslation M)
    (G : EuclideanYangMillsOSPhysicalHamiltonianGenerator T)
    (E : EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer T)
    (hMass : E.mass = exactGapValueReal)
    (B : ExplicitWightmanOSCanonicalPVMOpenSupportBridge M.toExplicitModel)
    (hRelGap :
      HasRelativisticMassGap M.energyMomentumSpectrum exactGapValueReal)
    (hClose : ∀ ε : ℝ, 0 < ε →
      ∃ energy ∈ M.toExplicitModel.vacuumOrthogonalPVMOpenSupport,
        energy < exactGapValueReal + ε) :
    EuclideanYangMillsOSPhysicalGeneratorSharpPVMOpenSupportRealResolventProp T :=
  euclidean_yang_mills_os_finite_volume_transfer_sharp_support_real_resolvent
    T G E.toFiniteVolumeVacuumGapTransfer hMass B hRelGap hClose

end EuclideanYangMillsOSPhysicalEmbeddedFiniteVolumeVacuumGapTransfer

end

end MathlibAnalytic
end MGAP4D
