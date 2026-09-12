import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumGapDerivedPhysicalMass
import Mathlib.Tactic

/-!
# Variational physical OS infrared mass

The statewise infrared effective mass

`physicalCorrelationRealClampInfraredEffectiveMass psi`

is already constructed for every physical state.  This file forms its
state-independent variational lower edge over all nonzero states orthogonal to
the physical vacuum.

This is deliberately distinct from the variational mass of the graph-closed
Hamiltonian.  No equality between the two quantities is assumed here.  The
first result is instead the robust direction supplied by the existing vacuum
transfer estimate: every `VacuumSemigroupGapSlope.mass` is a lower bound for
every statewise infrared exponent, hence also for their infimum.

No spectral theorem, PVM hypothesis, numerical mass value, or new physical
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

/-- Statewise infrared OS masses carried by nonzero physical excitations. -/
def physicalYangMillsOSInfraredMassSet
    (T : P.StronglyContinuousPhysicalSemigroup) : Set ℝ :=
  {r : ℝ |
    ∃ psi : P.PhysicalHilbert,
      psi ≠ 0 ∧
      inner ℝ psi P.vacuum = 0 ∧
      T.physicalCorrelationRealClampInfraredEffectiveMass psi = r}

/-- The state-independent physical OS infrared mass is the variational lower
edge of all nonzero vacuum-orthogonal statewise infrared exponents. -/
def physicalYangMillsOSInfraredMass
    (T : P.StronglyContinuousPhysicalSemigroup) : ℝ :=
  sInf T.physicalYangMillsOSInfraredMassSet

/-- A genuine closed-domain physical excitation makes the OS infrared mass set
nonempty. -/
theorem PhysicalYangMillsExcitationDomainWitness.osInfraredMassSet_nonempty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    T.physicalYangMillsOSInfraredMassSet.Nonempty := by
  refine ⟨T.physicalCorrelationRealClampInfraredEffectiveMass
      (W.state : P.PhysicalHilbert), ?_⟩
  exact ⟨(W.state : P.PhysicalHilbert), W.state_ne_zero,
    W.state_orthogonal, rfl⟩

/-- Inner symmetry makes zero a lower bound for every statewise infrared OS
mass. -/
theorem physicalYangMillsOSInfraredMassSet_lower_bound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {r : ℝ} (hr : r ∈ T.physicalYangMillsOSInfraredMassSet) :
    0 ≤ r := by
  rcases hr with ⟨psi, hpsi_ne, _hpsi, rfl⟩
  exact T.physicalCorrelationRealClampInfraredEffectiveMass_nonneg
    hSymmetric hpsi_ne

/-- Hence the statewise infrared OS mass set is bounded below. -/
theorem physicalYangMillsOSInfraredMassSet_bddBelow
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    BddBelow T.physicalYangMillsOSInfraredMassSet := by
  exact ⟨0, fun _ hr =>
    T.physicalYangMillsOSInfraredMassSet_lower_bound hSymmetric hr⟩

/-- The variational OS infrared mass is nonnegative whenever a genuine
excitation-domain witness exists. -/
theorem physicalYangMillsOSInfraredMass_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 ≤ T.physicalYangMillsOSInfraredMass := by
  unfold physicalYangMillsOSInfraredMass
  exact le_csInf W.osInfraredMassSet_nonempty
    (fun _ hr =>
      T.physicalYangMillsOSInfraredMassSet_lower_bound hSymmetric hr)

/-- The variational infrared mass lies below every statewise infrared exponent
in the physical excitation sector. -/
theorem physicalYangMillsOSInfraredMass_le_statewise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {psi : P.PhysicalHilbert}
    (hpsi_ne : psi ≠ 0)
    (hpsi : inner ℝ psi P.vacuum = 0) :
    T.physicalYangMillsOSInfraredMass ≤
      T.physicalCorrelationRealClampInfraredEffectiveMass psi := by
  unfold physicalYangMillsOSInfraredMass
  apply csInf_le (T.physicalYangMillsOSInfraredMassSet_bddBelow hSymmetric)
  exact ⟨psi, hpsi_ne, hpsi, rfl⟩

/-- A continuum vacuum transfer slope is a lower bound for the variational
physical OS infrared mass. -/
theorem VacuumSemigroupGapSlope.mass_le_physicalYangMillsOSInfraredMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsOSInfraredMass := by
  unfold physicalYangMillsOSInfraredMass
  apply le_csInf W.osInfraredMassSet_nonempty
  intro r hr
  rcases hr with ⟨psi, hpsi_ne, hpsi, rfl⟩
  exact G.mass_le_infraredEffectiveMass T hSymmetric hpsi hpsi_ne

/-- Thus the new variational OS infrared mass carries a strictly positive lower
bound whenever a vacuum transfer slope is available. -/
theorem VacuumSemigroupGapSlope.mass_pos_and_le_physicalYangMillsOSInfraredMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < G.mass ∧ G.mass ≤ T.physicalYangMillsOSInfraredMass := by
  exact ⟨G.mass_pos,
    G.mass_le_physicalYangMillsOSInfraredMass T hSymmetric W⟩

/-- Finite-volume transfer data give the same variational infrared lower bound
through their associated continuum vacuum slope. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsOSInfraredMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    G.mass ≤ T.physicalYangMillsOSInfraredMass := by
  exact G.toVacuumSemigroupGapSlope.mass_le_physicalYangMillsOSInfraredMass
    T hSymmetric W

/-- After self-adjoint reconstruction, nontriviality of the complete excitation
Hilbert space supplies the witness needed for the variational OS infrared
mass. -/
theorem VacuumSemigroupGapSlope.mass_le_physicalYangMillsOSInfraredMass_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    G.mass ≤ T.physicalYangMillsOSInfraredMass := by
  exact G.mass_le_physicalYangMillsOSInfraredMass T hSymmetric
    (T.physicalYangMillsExcitationDomainWitness_of_nontrivial hP hSelf)

/-- Finite-volume wrapper for the self-adjoint/nontrivial excitation-sector
variational infrared bound. -/
theorem FiniteVolumeVacuumGapTransfer.mass_le_physicalYangMillsOSInfraredMass_of_nontrivial
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    [Nontrivial P.VacuumOrthogonalHilbert] :
    G.mass ≤ T.physicalYangMillsOSInfraredMass := by
  exact G.toVacuumSemigroupGapSlope.mass_le_physicalYangMillsOSInfraredMass_of_nontrivial
    T hP hSymmetric hSelf

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
