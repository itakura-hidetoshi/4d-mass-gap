import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianNonnegative
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

/-- The Rayleigh quotient of the actual graph-closed OS Yang--Mills Hamiltonian.

This definition contains no prescribed mass scale.  In particular, no exact
numerical value is inserted before the Yang--Mills Hamiltonian has been
constructed. -/
def physicalYangMillsClosedRayleighQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.closedRightHamiltonian.domain) : ℝ :=
  inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) /
    ‖(psi : P.PhysicalHilbert)‖ ^ 2

/-- Rayleigh values carried by nonzero states in the physical excitation
sector.  Vacuum orthogonality is imposed on the actual completed OS Hilbert
space; it is not represented by a synthetic spectral carrier. -/
def physicalYangMillsClosedExcitationRayleighSet
    (T : P.StronglyContinuousPhysicalSemigroup) : Set ℝ :=
  {r : ℝ |
    ∃ psi : T.closedRightHamiltonian.domain,
      (psi : P.PhysicalHilbert) ≠ 0 ∧
      inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 ∧
      T.physicalYangMillsClosedRayleighQuotient psi = r}

/-- The physical Yang--Mills mass associated with the constructed OS
Hamiltonian is the variational lower edge of its non-vacuum Rayleigh values.

The definition is intentionally independent of any proposed exact value such
as `33/20`.  A numerical equality must be proved downstream from Yang--Mills
data. -/
def physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup) : ℝ :=
  sInf T.physicalYangMillsClosedExcitationRayleighSet

/-- Explicit existence datum for a nonzero excitation already lying in the
closed Hamiltonian domain.  This isolates nontriviality of the physical
excitation sector as a genuine construction obligation rather than hiding it
inside the definition of the mass. -/
structure PhysicalYangMillsExcitationDomainWitness
    (T : P.StronglyContinuousPhysicalSemigroup) where
  state : T.closedRightHamiltonian.domain
  state_ne_zero : (state : P.PhysicalHilbert) ≠ 0
  state_orthogonal : inner ℝ (state : P.PhysicalHilbert) P.vacuum = 0

/-- The closed Yang--Mills Hamiltonian has nonnegative Rayleigh quotient on
every nonzero domain vector. -/
theorem physicalYangMillsClosedRayleighQuotient_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.closedRightHamiltonian.domain) :
    0 ≤ T.physicalYangMillsClosedRayleighQuotient psi := by
  unfold physicalYangMillsClosedRayleighQuotient
  exact div_nonneg
    (T.closedRightHamiltonian_inner_nonneg psi)
    (sq_nonneg ‖(psi : P.PhysicalHilbert)‖)

/-- Consequently zero is a lower bound for every physical excitation Rayleigh
value. -/
theorem physicalYangMillsClosedExcitationRayleighSet_lower_bound
    (T : P.StronglyContinuousPhysicalSemigroup)
    {r : ℝ}
    (hr : r ∈ T.physicalYangMillsClosedExcitationRayleighSet) :
    0 ≤ r := by
  rcases hr with ⟨psi, _hpsi, _horthogonal, rfl⟩
  exact T.physicalYangMillsClosedRayleighQuotient_nonneg psi

/-- The actual excitation Rayleigh set is bounded below without any mass-gap
assumption. -/
theorem physicalYangMillsClosedExcitationRayleighSet_bddBelow
    (T : P.StronglyContinuousPhysicalSemigroup) :
    BddBelow T.physicalYangMillsClosedExcitationRayleighSet := by
  exact ⟨0, fun _ hr =>
    T.physicalYangMillsClosedExcitationRayleighSet_lower_bound hr⟩

/-- A genuine nonzero excitation-domain witness makes the variational set
nonempty. -/
theorem PhysicalYangMillsExcitationDomainWitness.rayleighSet_nonempty
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    T.physicalYangMillsClosedExcitationRayleighSet.Nonempty := by
  refine ⟨T.physicalYangMillsClosedRayleighQuotient W.state, ?_⟩
  exact ⟨W.state, W.state_ne_zero, W.state_orthogonal, rfl⟩

/-- The mass produced by the actual closed Yang--Mills Hamiltonian is
nonnegative as soon as the excitation sector contains a nonzero domain state. -/
theorem physicalYangMillsMass_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 ≤ T.physicalYangMillsMass := by
  unfold physicalYangMillsMass
  exact le_csInf W.rayleighSet_nonempty
    (fun _ hr =>
      T.physicalYangMillsClosedExcitationRayleighSet_lower_bound hr)

/-- The derived Yang--Mills mass is below every actual non-vacuum Rayleigh
value. -/
theorem physicalYangMillsMass_le_rayleigh
    (T : P.StronglyContinuousPhysicalSemigroup)
    {r : ℝ}
    (hr : r ∈ T.physicalYangMillsClosedExcitationRayleighSet) :
    T.physicalYangMillsMass ≤ r := by
  unfold physicalYangMillsMass
  exact csInf_le
    T.physicalYangMillsClosedExcitationRayleighSet_bddBelow hr

/-- Variational form on an individual nonzero excitation-domain vector. -/
theorem physicalYangMillsMass_mul_norm_sq_le_inner
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : (psi : P.PhysicalHilbert) ≠ 0)
    (horthogonal : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    T.physicalYangMillsMass * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi) (psi : P.PhysicalHilbert) := by
  have hmember :
      T.physicalYangMillsClosedRayleighQuotient psi ∈
        T.physicalYangMillsClosedExcitationRayleighSet :=
    ⟨psi, hpsi, horthogonal, rfl⟩
  have hInf := T.physicalYangMillsMass_le_rayleigh hmember
  have hden : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hpsi)
  unfold physicalYangMillsClosedRayleighQuotient at hInf
  exact (le_div_iff₀ hden).mp hInf

/-- Any uniform Rayleigh lower bound proved from Yang--Mills dynamics lies below
the mass defined by the actual Hamiltonian.  This is the correct direction for
finite-volume transfer estimates: they derive information about the physical
mass rather than defining it. -/
theorem uniformRayleighLowerBound_le_physicalYangMillsMass
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness)
    {m : ℝ}
    (hLower :
      ∀ psi : T.closedRightHamiltonian.domain,
        (psi : P.PhysicalHilbert) ≠ 0 →
        inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
        m * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
          inner ℝ (T.closedRightHamiltonian psi)
            (psi : P.PhysicalHilbert)) :
    m ≤ T.physicalYangMillsMass := by
  unfold physicalYangMillsMass
  apply le_csInf W.rayleighSet_nonempty
  intro r hr
  rcases hr with ⟨psi, hpsi, horthogonal, rfl⟩
  have hden : 0 < ‖(psi : P.PhysicalHilbert)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hpsi)
  unfold physicalYangMillsClosedRayleighQuotient
  exact (le_div_iff₀ hden).2 (hLower psi hpsi horthogonal)

/-- Positivity of the derived physical mass is exactly equivalent to existence
of some strictly positive uniform Rayleigh lower bound on the actual
vacuum-orthogonal Hamiltonian domain. -/
theorem physicalYangMillsMass_pos_iff_exists_uniformRayleighLowerBound
    (T : P.StronglyContinuousPhysicalSemigroup)
    (W : T.PhysicalYangMillsExcitationDomainWitness) :
    0 < T.physicalYangMillsMass ↔
      ∃ m : ℝ, 0 < m ∧
        ∀ psi : T.closedRightHamiltonian.domain,
          (psi : P.PhysicalHilbert) ≠ 0 →
          inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0 →
          m * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
            inner ℝ (T.closedRightHamiltonian psi)
              (psi : P.PhysicalHilbert) := by
  constructor
  · intro hmass
    refine ⟨T.physicalYangMillsMass, hmass, ?_⟩
    intro psi hpsi horthogonal
    exact T.physicalYangMillsMass_mul_norm_sq_le_inner
      psi hpsi horthogonal
  · rintro ⟨m, hm, hLower⟩
    exact lt_of_lt_of_le hm
      (T.uniformRayleighLowerBound_le_physicalYangMillsMass W hLower)

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
