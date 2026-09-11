import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSDerivedMassExcitationWitness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedMassGapTransfer
import Mathlib.Tactic

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

/-- A continuum vacuum-sector transfer slope does not define the physical mass.
Instead, once propagated to the actual closed OS Hamiltonian, its mass parameter
is a rigorous lower bound for the variational Yang--Mills mass. -/
theorem VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsMass := by
  apply T.uniformRayleighLowerBound_le_physicalYangMillsMass W
  intro psi _hpsi horthogonal
  exact G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    T hP psi horthogonal

/-- In particular, a finite-volume transfer package supplies only a lower bound
on the mass derived from the actual continuum Hamiltonian. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsMass := by
  apply T.uniformRayleighLowerBound_le_physicalYangMillsMass W
  intro psi _hpsi horthogonal
  exact G.closedRightHamiltonian_inner_ge_mass_mul_norm_sq
    T hP psi horthogonal

/-- A positive continuum transfer slope therefore proves positivity of the
mass derived from the actual Yang--Mills Hamiltonian. -/
theorem VacuumSemigroupGapSlope.physicalYangMillsMass_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < T.physicalYangMillsMass :=
  lt_of_lt_of_le G.mass_pos
    (G.mass_le_physicalYangMillsMass T hP W)

/-- The same conclusion directly from the finite-volume transfer package. -/
theorem FiniteVolumeVacuumGapTransfer.physicalYangMillsMass_pos
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < T.physicalYangMillsMass :=
  lt_of_lt_of_le G.mass_pos
    (G.mass_le_physicalYangMillsMass T hP W)

/-- After self-adjoint reconstruction, nontriviality of the physical excitation
Hilbert space is enough to turn a continuum transfer estimate into a lower bound
on the derived mass. -/
theorem VacuumSemigroupGapSlope.mass_le_physicalYangMillsMass_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    G.mass ≤ T.physicalYangMillsMass :=
  G.mass_le_physicalYangMillsMass T hP
    (T.physicalYangMillsExcitationDomainWitness_of_nontrivial hP hSelf)

/-- Finite Wilson/transfer data therefore prove a physical Yang--Mills mass
lower bound once the reconstructed excitation sector is known to be nontrivial. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsMass_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    G.mass ≤ T.physicalYangMillsMass :=
  G.mass_le_physicalYangMillsMass T hP
    (T.physicalYangMillsExcitationDomainWitness_of_nontrivial hP hSelf)

/-- Hence any positive continuum transfer gap implies a positive physical
Yang--Mills mass without assigning a numerical value in advance. -/
theorem VacuumSemigroupGapSlope.physicalYangMillsMass_pos_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    0 < T.physicalYangMillsMass :=
  lt_of_lt_of_le G.mass_pos
    (G.mass_le_physicalYangMillsMass_of_nontrivial T hP hSelf)

/-- Finite-volume positivity has the same physical interpretation. -/
theorem FiniteVolumeVacuumGapTransfer.physicalYangMillsMass_pos_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    0 < T.physicalYangMillsMass :=
  lt_of_lt_of_le G.mass_pos
    (G.mass_le_physicalYangMillsMass_of_nontrivial T hP hSelf)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
