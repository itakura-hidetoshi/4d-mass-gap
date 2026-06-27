import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSApproximatingVacuumOrthogonalSemigroup

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

/-- A common-carrier convergence bridge from the actual finite-volume Wilson OS
Hilbert spaces to one completed continuum OS Hilbert space.

The finite spaces, normalized vacua, and transfer operators are no longer
abstract placeholders: they are the scale-dependent OS completions generated
by the embedded even-periodic Wilson Gibbs states.  The remaining convergence
input is expressed by continuous linear approximation and embedding maps into
the common continuum carrier. -/
structure PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
    (S : PhysicalFourDimensionalYangMillsSymmetryLimit)
    (D : PhysicalYangMillsGaugeInvariantOSReflectionData S)
    (halfExtent : ℕ → ℕ)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (hbeta : ∀ n, 0 ≤ beta n)
    (B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta)
    (hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n))
    (P : D.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup)
    (C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant)
    (G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C) where
  approximate :
    (n : ℕ) → P.PhysicalHilbert →L[ℝ]
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n
  embed :
    (n : ℕ) →
      PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
          S D halfExtent N hN beta hbeta B hInvariant n →L[ℝ]
        P.PhysicalHilbert
  embed_norm :
    ∀ (n : ℕ)
      (phi : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
        S D halfExtent N hN beta hbeta B hInvariant n),
      ‖embed n phi‖ = ‖phi‖
  approximate_orthogonal :
    ∀ (n : ℕ) (psi : P.PhysicalHilbert),
      inner ℝ psi P.vacuum = 0 →
        inner ℝ (approximate n psi)
          (physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
            S D halfExtent N hN beta hbeta B hInvariant n) = 0
  approximate_tendsto :
    ∀ psi : P.PhysicalHilbert,
      Tendsto
        (fun n : ℕ => embed n (approximate n psi))
        atTop
        (nhds psi)
  evolved_tendsto :
    ∀ (t : NNReal) (psi : P.PhysicalHilbert),
      Tendsto
        (fun n : ℕ =>
          embed n (C.finiteOperator n t (approximate n psi)))
        atTop
        (nhds (T.toPhysicalSemigroup.operator t psi))

namespace PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {halfExtent : ℕ → ℕ}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    {B : PhysicalYangMillsEvenPeriodicWilsonOSWeakStarBridge
      S D halfExtent N hN beta hbeta}
    {hInvariant : ∀ n,
      D.WeakStarReflectionInvariant
        (physicalYangMillsApproximatingGaugeInvariantWeakStarState S n)}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {C : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingSemigroupFamily
      S D halfExtent N hN beta hbeta B hInvariant}
    {G : PhysicalYangMillsEvenPeriodicWilsonOSApproximatingVacuumGapCertificate
      S D halfExtent N hN beta hbeta B hInvariant C}

/-- The concrete Wilson common-carrier bridge instantiates the abstract embedded
finite-volume gap-transfer package. -/
noncomputable def toEmbeddedFiniteVolumeVacuumGapTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G) :
    T.EmbeddedFiniteVolumeVacuumGapTransfer where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  FiniteState := fun n =>
    PhysicalYangMillsEvenPeriodicWilsonOSApproximatingHilbert
      S D halfExtent N hN beta hbeta B hInvariant n
  finiteNormedAddCommGroup := fun _ => inferInstance
  finiteInnerProductSpace := fun _ => inferInstance
  finiteVacuum := fun n =>
    physical_yang_mills_evenPeriodicWilsonOS_approximating_vacuum
      S D halfExtent N hN beta hbeta B hInvariant n
  finiteOperator := C.finiteOperator
  approximate := A.approximate
  embed := A.embed
  embed_norm := A.embed_norm
  approximate_orthogonal := A.approximate_orthogonal
  approximate_tendsto := A.approximate_tendsto
  evolved_tendsto := A.evolved_tendsto
  finite_decay := G.finite_decay

/-- The actual Wilson OS Hilbert-space bridge also supplies the original scalar
finite-volume transfer package. -/
noncomputable def toFiniteVolumeVacuumGapTransfer
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G) :
    T.FiniteVolumeVacuumGapTransfer :=
  A.toEmbeddedFiniteVolumeVacuumGapTransfer.toFiniteVolumeVacuumGapTransfer

/-- The actual finite Wilson OS transfer operators imply the continuum
right-Hamiltonian Rayleigh lower bound on the vacuum-orthogonal generator
domain. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact
    A.toEmbeddedFiniteVolumeVacuumGapTransfer
      |>.rightHamiltonian_inner_ge_mass_mul_norm_sq psi hpsi

/-- The same lower bound survives graph closure of the continuum OS
Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact
    A.toEmbeddedFiniteVolumeVacuumGapTransfer
      |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq hP psi hpsi

/-- Under the actual Wilson common-carrier gap bridge, the zero-energy space of
the continuum graph-closed OS Hamiltonian is exactly the normalized vacuum
line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (A : PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer
      S D halfExtent N hN beta hbeta B hInvariant P T C G)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact
    A.toEmbeddedFiniteVolumeVacuumGapTransfer
      |>.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum hP psi

end PhysicalYangMillsEvenPeriodicWilsonOSCommonCarrierGapTransfer

end MathlibAnalytic
end MGAP4D

end
