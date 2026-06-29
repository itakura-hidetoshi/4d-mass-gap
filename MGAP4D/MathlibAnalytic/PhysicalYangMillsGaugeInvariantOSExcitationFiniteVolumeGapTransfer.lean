import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteVolumeMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCore

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

/-- A finite-volume transfer bridge formulated directly on varying excitation
Hilbert spaces.  Unlike `FiniteVolumeVacuumGapTransfer`, it does not reinsert a
finite vacuum line: every finite carrier already represents the
vacuum-orthogonal sector. -/
structure ExcitationFiniteVolumeGapTransfer
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
  approximate_norm_tendsto :
    ∀ psi : P.VacuumOrthogonalHilbert,
      Tendsto
        (fun n : ℕ => ‖approximate n psi‖)
        atTop
        (nhds ‖psi‖)
  evolved_norm_tendsto :
    ∀ (t : NNReal) (psi : P.VacuumOrthogonalHilbert),
      Tendsto
        (fun n : ℕ => ‖finiteOperator n t (approximate n psi)‖)
        atTop
        (nhds
          ‖T.toPhysicalSemigroup.operator t
            (psi : P.PhysicalHilbert)‖)
  finite_decay :
    ∀ (n : ℕ) (t : NNReal) (phi : FiniteExcitation n),
      ‖finiteOperator n t phi‖ ≤ decayFactor t * ‖phi‖

attribute [instance]
  ExcitationFiniteVolumeGapTransfer.finiteNormedAddCommGroup
  ExcitationFiniteVolumeGapTransfer.finiteInnerProductSpace

namespace ExcitationFiniteVolumeGapTransfer

variable {T : P.StronglyContinuousPhysicalSemigroup}

/-- Scalar norm convergence transfers an excitation-only finite-volume decay
estimate to the continuum vacuum-orthogonal semigroup sector. -/
noncomputable def toVacuumSemigroupGapSlope
    (G : T.ExcitationFiniteVolumeGapTransfer) :
    T.VacuumSemigroupGapSlope where
  mass := G.mass
  mass_pos := G.mass_pos
  decayFactor := G.decayFactor
  slope_tendsto := G.slope_tendsto
  decay := by
    intro t psi hpsi
    let psiOrthogonal : P.VacuumOrthogonalHilbert :=
      ⟨psi, (P.mem_vacuumOrthogonal_iff psi).2
        ((real_inner_comm P.vacuum psi).symm.trans hpsi)⟩
    apply le_of_tendsto_of_tendsto
      (G.evolved_norm_tendsto t psiOrthogonal)
      (tendsto_const_nhds.mul
        (G.approximate_norm_tendsto psiOrthogonal))
    exact Filter.Eventually.of_forall fun n =>
      G.finite_decay n t (G.approximate n psiOrthogonal)

/-- The excitation-only transfer bridge gives the continuum right-Hamiltonian
Rayleigh lower bound. -/
theorem rightHamiltonian_inner_ge_mass_mul_norm_sq
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.ExcitationFiniteVolumeGapTransfer)
    (psi : T.rightGeneratorDomain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    G.mass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.rightHamiltonian psi) (psi : P.PhysicalHilbert) :=
  VacuumSemigroupGapSlope.rightHamiltonian_inner_ge_mass_mul_norm_sq
    T G.toVacuumSemigroupGapSlope psi hpsi

end ExcitationFiniteVolumeGapTransfer
end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
