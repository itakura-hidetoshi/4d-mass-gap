import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumUniqueness
import Mathlib.Tactic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace MGAP4D
namespace MathlibAnalytic

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A concrete common-carrier criterion for finite-volume vacuum-gap transfer.

Each finite-volume Hilbert space is embedded isometrically into the completed
physical OS Hilbert space.  Instead of postulating convergence only after
applying the norm, this structure asks for convergence of the embedded state
vectors and of the embedded evolved vectors themselves.  Continuity of the
norm then produces the scalar convergence fields required by
`FiniteVolumeVacuumGapTransfer`.

This is the natural interface for an actual lattice construction: one proves
finite-volume orthogonality and decay before embedding, and proves convergence
of the embedded transfer trajectories in the common physical carrier. -/
structure EmbeddedFiniteVolumeVacuumGapTransfer
    (T : P.StronglyContinuousPhysicalSemigroup) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : NNReal → ℝ
  slope_tendsto :
    Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  FiniteState : ℕ → Type
  [finiteNormedAddCommGroup : ∀ n, NormedAddCommGroup (FiniteState n)]
  [finiteInnerProductSpace : ∀ n, InnerProductSpace ℝ (FiniteState n)]
  finiteVacuum : (n : ℕ) → FiniteState n
  finiteOperator :
    (n : ℕ) → NNReal → FiniteState n →L[ℝ] FiniteState n
  approximate :
    (n : ℕ) → P.PhysicalHilbert →L[ℝ] FiniteState n
  embed :
    (n : ℕ) → FiniteState n →L[ℝ] P.PhysicalHilbert
  embed_norm :
    ∀ (n : ℕ) (phi : FiniteState n), ‖embed n phi‖ = ‖phi‖
  approximate_orthogonal :
    ∀ (n : ℕ) (psi : P.PhysicalHilbert),
      inner ℝ psi P.vacuum = 0 →
        inner ℝ (approximate n psi) (finiteVacuum n) = 0
  approximate_tendsto :
    ∀ psi : P.PhysicalHilbert,
      Tendsto
        (fun n : ℕ => embed n (approximate n psi))
        atTop
        (nhds psi)
  evolved_tendsto :
    ∀ (t : NNReal) (psi : P.PhysicalHilbert),
      Tendsto
        (fun n : ℕ => embed n (finiteOperator n t (approximate n psi)))
        atTop
        (nhds (T.toPhysicalSemigroup.operator t psi))
  finite_decay :
    ∀ (n : ℕ) (t : NNReal) (phi : FiniteState n),
      inner ℝ phi (finiteVacuum n) = 0 →
        ‖finiteOperator n t phi‖ ≤ decayFactor t * ‖phi‖

attribute [instance]
  EmbeddedFiniteVolumeVacuumGapTransfer.finiteNormedAddCommGroup
  EmbeddedFiniteVolumeVacuumGapTransfer.finiteInnerProductSpace

namespace EmbeddedFiniteVolumeVacuumGapTransfer

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- Vector convergence through isometric common-carrier embeddings supplies the
scalar norm convergence package used by the existing finite-volume transfer
argument. -/
noncomputable def toFiniteVolumeVacuumGapTransfer
    (G : T.EmbeddedFiniteVolumeVacuumGapTransfer) :
    T.FiniteVolumeVacuumGapTransfer where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  FiniteState := G.FiniteState
  finiteNormedAddCommGroup := G.finiteNormedAddCommGroup
  finiteInnerProductSpace := G.finiteInnerProductSpace
  finiteVacuum := G.finiteVacuum
  finiteOperator := G.finiteOperator
  approximate := G.approximate
  approximate_orthogonal := G.approximate_orthogonal
  approximate_norm_tendsto := by
    intro psi
    have hnorm := (G.approximate_tendsto psi).norm
    simpa only [G.embed_norm] using hnorm
  evolved_norm_tendsto := by
    intro t psi
    have hnorm := (G.evolved_tendsto t psi).norm
    simpa only [G.embed_norm] using hnorm
  finite_decay := G.finite_decay

/-- The embedded finite-volume package directly yields a continuum vacuum-sector
semigroup gap slope. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : T.EmbeddedFiniteVolumeVacuumGapTransfer) :
    T.VacuumSemigroupGapSlope :=
  G.toFiniteVolumeVacuumGapTransfer.toVacuumSemigroupGapSlope

/-- The common-carrier finite-volume transfer criterion gives the canonical
right-Hamiltonian Rayleigh lower bound on the vacuum-orthogonal generator
domain. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.EmbeddedFiniteVolumeVacuumGapTransfer)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact G.toFiniteVolumeVacuumGapTransfer
    |>.rightHamiltonian_inner_ge_mass_mul_norm_sq T psi hpsi

/-- The embedded transfer criterion passes the same positive lower bound through
Mathlib's graph closure. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.EmbeddedFiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact G.toFiniteVolumeVacuumGapTransfer
    |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq T hP psi hpsi

/-- Under the embedded finite-volume transfer criterion, the zero-energy
subspace of the graph-closed OS Hamiltonian is exactly the normalized vacuum
line. -/
theorem closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum
    (G : T.EmbeddedFiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain) :
    T.closedRightHamiltonian psi = 0 ↔
      (psi : P.PhysicalHilbert) =
        (inner ℝ (psi : P.PhysicalHilbert) P.vacuum) • P.vacuum := by
  exact G.toFiniteVolumeVacuumGapTransfer
    |>.closedRightHamiltonian_eq_zero_iff_eq_inner_smul_vacuum T hP psi

end EmbeddedFiniteVolumeVacuumGapTransfer
end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
