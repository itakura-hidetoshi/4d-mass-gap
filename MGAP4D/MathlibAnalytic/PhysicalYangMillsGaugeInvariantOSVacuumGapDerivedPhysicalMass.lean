import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedRayleighMass
import Mathlib.Tactic

/-!
# Vacuum OS gap slope as a lower bound for the derived physical Yang--Mills mass

The graph-closed right Hamiltonian already satisfies the vacuum-sector
quadratic-form coercive estimate supplied by `VacuumSemigroupGapSlope`.
Independently, the physical Yang--Mills mass is defined variationally as the
infimum of Rayleigh quotients of nonzero vacuum-orthogonal vectors in the
actual closed Hamiltonian domain.

This file connects those two existing layers.  Once a genuine excitation-domain
witness is available, the closed coercive estimate is a uniform Rayleigh lower
bound, hence

`0 < G.mass <= T.physicalYangMillsMass`.

Thus positivity carried by the vacuum OS transfer slope propagates to the
actual variational mass of the graph-closed physical Hamiltonian.  No numerical
mass value, spectral-attainment assumption, PVM hypothesis, or new Yang--Mills
axiom is introduced.
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

/-- A vacuum OS gap slope is a uniform lower bound for the variational mass of
the actual graph-closed physical Hamiltonian. -/
theorem VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsMass := by
  apply T.uniformRayleighLowerBound_le_physicalYangMillsMass W
  intro psi _hpsi horthogonal
  exact
    VacuumSemigroupGapSlope.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
      T G hP psi horthogonal

/-- The transfer slope and the actual variational physical mass therefore form
a strictly positive lower-bound chain. -/
theorem VacuumSemigroupGapSlope.mass_pos_and_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧ G.mass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass T G hP W⟩

/-- In particular, existence of a positive vacuum OS gap slope proves
positivity of the mass defined from the actual graph-closed Hamiltonian. -/
theorem VacuumSemigroupGapSlope.physicalYangMillsMass_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < T.physicalYangMillsMass := by
  exact lt_of_lt_of_le G.mass_pos
    (VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass T G hP W)

/-- The finite-volume transfer package gives the same lower bound on the
variational physical mass through its associated vacuum OS gap slope. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsMass := by
  exact
    VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass
      T G.toVacuumSemigroupGapSlope hP W

/-- Finite-volume transfer data therefore expose a strictly positive lower
bound for the actual variational physical mass. -/
theorem FiniteVolumeVacuumGapTransfer.mass_pos_and_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧ G.mass ≤ T.physicalYangMillsMass := by
  exact ⟨G.mass_pos,
    FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsMass T G hP W⟩

/-- Positivity of the actual variational physical mass follows immediately
from finite-volume vacuum-gap transfer data. -/
theorem FiniteVolumeVacuumGapTransfer.physicalYangMillsMass_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < T.physicalYangMillsMass := by
  exact lt_of_lt_of_le G.mass_pos
    (FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsMass T G hP W)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
