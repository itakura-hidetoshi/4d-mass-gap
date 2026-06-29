import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExcitationFiniteVolumeGapTransfer

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

/-- A common-carrier finite-volume gap transfer formulated directly on varying
excitation Hilbert spaces.  Vector convergence after isometric embedding is the
only convergence input; scalar norm convergence is derived automatically. -/
structure ExcitationEmbeddedFiniteVolumeGapTransfer
    (T : P.StronglyContinuousPhysicalSemigroup) where
  mass : ℝ
  mass_pos : 0 < mass
  decayFactor : NNReal → ℝ
  slope_tendsto :
    Tendsto
      (fun t : NNReal => (t : ℝ)⁻¹ * (1 - decayFactor t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass)
  FiniteExcitation : ℕ → Type
  [finiteNormedAddCommGroup : ∀ n, NormedAddCommGroup (FiniteExcitation n)]
  [finiteInnerProductSpace : ∀ n, InnerProductSpace ℝ (FiniteExcitation n)]
  finiteOperator :
    (n : ℕ) → NNReal →
      FiniteExcitation n →L[ℝ] FiniteExcitation n
  approximate :
    (n : ℕ) → P.VacuumOrthogonalHilbert →L[ℝ] FiniteExcitation n
  embed :
    (n : ℕ) → FiniteExcitation n →L[ℝ] P.PhysicalHilbert
  embed_norm :
    ∀ (n : ℕ) (phi : FiniteExcitation n), ‖embed n phi‖ = ‖phi‖
  approximate_tendsto :
    ∀ psi : P.VacuumOrthogonalHilbert,
      Tendsto
        (fun n : ℕ => embed n (approximate n psi))
        atTop
        (nhds (psi : P.PhysicalHilbert))
  evolved_tendsto :
    ∀ (t : NNReal) (psi : P.VacuumOrthogonalHilbert),
      Tendsto
        (fun n : ℕ => embed n (finiteOperator n t (approximate n psi)))
        atTop
        (nhds
          (T.toPhysicalSemigroup.operator t
            (psi : P.PhysicalHilbert)))
  finite_decay :
    ∀ (n : ℕ) (t : NNReal) (phi : FiniteExcitation n),
      ‖finiteOperator n t phi‖ ≤ decayFactor t * ‖phi‖

attribute [instance]
  ExcitationEmbeddedFiniteVolumeGapTransfer.finiteNormedAddCommGroup
  ExcitationEmbeddedFiniteVolumeGapTransfer.finiteInnerProductSpace

namespace ExcitationEmbeddedFiniteVolumeGapTransfer

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- Isometric common-carrier vector convergence supplies the scalar convergence
package required by the excitation-only OS gap transfer. -/
noncomputable def toExcitationFiniteVolumeGapTransfer
    (G : T.ExcitationEmbeddedFiniteVolumeGapTransfer) :
    T.ExcitationFiniteVolumeGapTransfer where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  FiniteExcitation := G.FiniteExcitation
  finiteNormedAddCommGroup := G.finiteNormedAddCommGroup
  finiteInnerProductSpace := G.finiteInnerProductSpace
  finiteOperator := G.finiteOperator
  approximate := G.approximate
  approximate_norm_tendsto := by
    intro psi
    have hnorm := (G.approximate_tendsto psi).norm
    simpa only [G.embed_norm] using hnorm
  evolved_norm_tendsto := by
    intro t psi
    have hnorm := (G.evolved_tendsto t psi).norm
    simpa only [G.embed_norm] using hnorm
  finite_decay := G.finite_decay

/-- The embedded excitation transfer gives the continuum vacuum-sector gap
slope. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : T.ExcitationEmbeddedFiniteVolumeGapTransfer) :
    T.VacuumSemigroupGapSlope :=
  G.toExcitationFiniteVolumeGapTransfer.toVacuumSemigroupGapSlope

/-- Common-carrier excitation convergence transfers the finite gap to the
continuum right Hamiltonian. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.ExcitationEmbeddedFiniteVolumeGapTransfer)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) :=
  G.toExcitationFiniteVolumeGapTransfer.
    rightHamiltonian_inner_ge_mass_mul_norm_sq T psi hpsi

/-- The embedded excitation gap survives graph closure of the OS Hamiltonian. -/
theorem closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    (G : T.ExcitationEmbeddedFiniteVolumeGapTransfer)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) :=
  G.toExcitationFiniteVolumeGapTransfer
    |>.toVacuumSemigroupGapSlope
    |>.closedRightHamiltonian_inner_ge_mass_mul_norm_sq T hP psi hpsi

end ExcitationEmbeddedFiniteVolumeGapTransfer
end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
