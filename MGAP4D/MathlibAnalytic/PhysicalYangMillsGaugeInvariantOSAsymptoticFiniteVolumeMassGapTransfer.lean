import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Finite-volume vacuum-gap transfer with a scale-dependent decay factor.

Unlike `FiniteVolumeVacuumGapTransfer`, the finite estimate is allowed to use
`finiteDecayFactor n t`; only its limit is required to be the continuum
`decayFactor t`.  This is the natural interface for lattice-time selectors such
as `floor (t / a_n)`, where the finite operator acts at a nearby realizable time
rather than at exactly `t`.

No finite-time semigroup law is required by this structure. -/
structure AsymptoticFiniteVolumeVacuumGapTransfer
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
  finiteDecayFactor : ℕ → NNReal → ℝ
  finiteDecayFactor_tendsto :
    ∀ t : NNReal,
      Tendsto (fun n : ℕ => finiteDecayFactor n t)
        atTop (nhds (decayFactor t))
  approximate :
    (n : ℕ) → P.PhysicalHilbert →L[ℝ] FiniteState n
  approximate_orthogonal :
    ∀ (n : ℕ) (psi : P.PhysicalHilbert),
      inner ℝ psi P.vacuum = 0 →
        inner ℝ (approximate n psi) (finiteVacuum n) = 0
  approximate_norm_tendsto :
    ∀ psi : P.PhysicalHilbert,
      Tendsto (fun n : ℕ => ‖approximate n psi‖)
        atTop (nhds ‖psi‖)
  evolved_norm_tendsto :
    ∀ (t : NNReal) (psi : P.PhysicalHilbert),
      Tendsto
        (fun n : ℕ => ‖finiteOperator n t (approximate n psi)‖)
        atTop
        (nhds ‖T.toPhysicalSemigroup.operator t psi‖)
  finite_decay :
    ∀ (n : ℕ) (t : NNReal) (phi : FiniteState n),
      inner ℝ phi (finiteVacuum n) = 0 →
        ‖finiteOperator n t phi‖ ≤
          finiteDecayFactor n t * ‖phi‖

attribute [instance]
  AsymptoticFiniteVolumeVacuumGapTransfer.finiteNormedAddCommGroup
  AsymptoticFiniteVolumeVacuumGapTransfer.finiteInnerProductSpace

namespace AsymptoticFiniteVolumeVacuumGapTransfer

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- A scale-dependent finite decay whose factor converges to the target
continuum decay passes to the completed continuum OS semigroup. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : T.AsymptoticFiniteVolumeVacuumGapTransfer) :
    T.VacuumSemigroupGapSlope where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  decay := by
    intro t psi hpsi
    apply le_of_tendsto_of_tendsto
      (G.evolved_norm_tendsto t psi)
      ((G.finiteDecayFactor_tendsto t).mul
        (G.approximate_norm_tendsto psi))
    exact Filter.Eventually.of_forall fun n =>
      G.finite_decay n t (G.approximate n psi)
        (G.approximate_orthogonal n psi hpsi)

/-- The asymptotic finite-volume package yields the canonical continuum
right-Hamiltonian Rayleigh lower bound. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.AsymptoticFiniteVolumeVacuumGapTransfer)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact VacuumSemigroupGapSlope.rightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope psi hpsi

/-- The same asymptotic gap passes through graph closure of the continuum
right Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.AsymptoticFiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope hP psi hpsi

end AsymptoticFiniteVolumeVacuumGapTransfer

/-- Common-carrier vector-convergence version of
`AsymptoticFiniteVolumeVacuumGapTransfer`.

Finite spaces are embedded isometrically into the continuum OS Hilbert space.
Vector convergence then theorem-generates the two norm-convergence fields used
by the scalar asymptotic transfer argument. -/
structure EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer
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
  finiteDecayFactor : ℕ → NNReal → ℝ
  finiteDecayFactor_tendsto :
    ∀ t : NNReal,
      Tendsto (fun n : ℕ => finiteDecayFactor n t)
        atTop (nhds (decayFactor t))
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
        ‖finiteOperator n t phi‖ ≤
          finiteDecayFactor n t * ‖phi‖

attribute [instance]
  EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer.finiteNormedAddCommGroup
  EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer.finiteInnerProductSpace

namespace EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- Isometric common-carrier convergence reduces to the scalar asymptotic
finite-volume transfer package. -/
noncomputable def toAsymptoticFiniteVolumeVacuumGapTransfer
    (G : T.EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer) :
    T.AsymptoticFiniteVolumeVacuumGapTransfer where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  FiniteState := G.FiniteState
  finiteNormedAddCommGroup := G.finiteNormedAddCommGroup
  finiteInnerProductSpace := G.finiteInnerProductSpace
  finiteVacuum := G.finiteVacuum
  finiteOperator := G.finiteOperator
  finiteDecayFactor := G.finiteDecayFactor
  finiteDecayFactor_tendsto := G.finiteDecayFactor_tendsto
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

/-- The embedded asymptotic package directly produces the continuum vacuum
semigroup gap. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : T.EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer) :
    T.VacuumSemigroupGapSlope :=
  G.toAsymptoticFiniteVolumeVacuumGapTransfer.toVacuumSemigroupGapSlope

/-- Common-carrier asymptotic transfer gives the continuum right-Hamiltonian
Rayleigh lower bound. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  exact G.toAsymptoticFiniteVolumeVacuumGapTransfer
    |>.rightHamiltonian_inner_ge_mass_mul_norm_sq psi hpsi

/-- Common-carrier asymptotic transfer preserves the same lower bound on the
closed Hamiltonian domain. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  exact G.toAsymptoticFiniteVolumeVacuumGapTransfer
    |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq hP psi hpsi

end EmbeddedAsymptoticFiniteVolumeVacuumGapTransfer
end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
