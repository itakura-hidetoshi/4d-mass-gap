import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumIRMassLower
import Mathlib.Tactic

/-!
# Vacuum OS gap slope below both infrared decay and derived physical mass

The repository already proves, separately, that a positive vacuum-sector transfer
slope lies below every nonzero vacuum-orthogonal infrared OS effective mass and
below the variational physical Yang--Mills mass of the actual graph-closed OS
Hamiltonian.

This file packages those two rigorously distinct consequences behind the same
transfer slope:

`0 < G.mass`,
`G.mass <= m_IR(psi)`,
`G.mass <= physicalYangMillsMass`.

The point is not to identify the infrared exponent with the variational mass.
No such equality is asserted here.  The theorem only records their common
positive lower bound, both with an explicit excitation-domain witness and with
the existing self-adjoint/nontrivial excitation-sector route.

No numerical mass value, spectral-attainment assumption, PVM hypothesis, or
new Yang--Mills axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- A vacuum transfer slope is a common strictly positive lower bound for both
the infrared OS exponent of a chosen nonzero excitation and the variational
mass of the actual closed physical Hamiltonian. -/
theorem VacuumSemigroupGapSlope.mass_ir_physicalYangMillsMass_lower_bounds
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧
      G.mass ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi ∧
      G.mass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    G.mass_le_infraredEffectiveMass T hSymmetric hpsi hpsi_ne,
    G.mass_le_physicalYangMillsMass T hP W⟩

/-- Finite-volume transfer data expose the same common lower bound through the
associated continuum vacuum-gap slope. -/
theorem FiniteVolumeVacuumGapTransfer.mass_ir_physicalYangMillsMass_lower_bounds
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧
      G.mass ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi ∧
      G.mass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    G.mass_le_infraredEffectiveMass T hSymmetric hpsi hpsi_ne,
    G.mass_le_physicalYangMillsMass T hP W⟩

/-- After self-adjoint reconstruction, nontriviality of the excitation Hilbert
space removes the need to pass an explicit excitation-domain witness when
recording the common infrared/variational lower bound. -/
theorem VacuumSemigroupGapSlope.mass_ir_physicalYangMillsMass_lower_bounds_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    0 < G.mass ∧
      G.mass ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi ∧
      G.mass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    G.mass_le_infraredEffectiveMass T hSymmetric hpsi hpsi_ne,
    G.mass_le_physicalYangMillsMass_of_nontrivial T hP hSelf⟩

/-- Finite-volume wrapper for the self-adjoint/nontrivial excitation-sector
version of the common lower-bound chain. -/
theorem FiniteVolumeVacuumGapTransfer.mass_ir_physicalYangMillsMass_lower_bounds_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {psi : P.PhysicalHilbert}
    (hpsi : inner ℝ psi P.vacuum = 0)
    (hpsi_ne : psi ≠ 0)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    0 < G.mass ∧
      G.mass ≤ T.physicalCorrelationRealClampInfraredEffectiveMass psi ∧
      G.mass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    G.mass_le_infraredEffectiveMass T hSymmetric hpsi hpsi_ne,
    G.mass_le_physicalYangMillsMass_of_nontrivial T hP hSelf⟩

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
