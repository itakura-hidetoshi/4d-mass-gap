import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSInfinitesimalGenerator

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The right Euclidean Hamiltonian difference quotient.  Its sign is opposite
to the infinitesimal generator quotient because physical Euclidean evolution is
written formally as `T_t = exp (-t H)`. -/
def rightHamiltonianDifferenceQuotient
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) : P.PhysicalHilbert :=
  (t : ℝ)⁻¹ • (psi - T.toPhysicalSemigroup.operator t psi)

/-- The Hamiltonian and infinitesimal-generator difference quotients differ by
one minus sign. -/
@[simp] theorem rightHamiltonianDifferenceQuotient_eq_neg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (t : NNReal) :
    T.rightHamiltonianDifferenceQuotient psi t =
      -T.rightDifferenceQuotient psi t := by
  simp only [rightHamiltonianDifferenceQuotient, rightDifferenceQuotient]
  module

/-- A vector has right Hamiltonian value `eta` exactly when its semigroup
infinitesimal-generator value is `-eta`. -/
def HasRightHamiltonianValue
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi eta : P.PhysicalHilbert) : Prop :=
  T.HasRightGeneratorValue psi (-eta)

/-- Right Hamiltonian values are unique. -/
theorem hasRightHamiltonianValue_unique
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi eta zeta : P.PhysicalHilbert}
    (heta : T.HasRightHamiltonianValue psi eta)
    (hzeta : T.HasRightHamiltonianValue psi zeta) :
    eta = zeta := by
  have hneg : -eta = -zeta :=
    T.hasRightGeneratorValue_unique heta hzeta
  exact neg_injective hneg

/-- The canonical right Hamiltonian on the semigroup generator domain.  This is
a densely-defined candidate only after density of the domain is supplied; no
self-adjointness claim is made here. -/
noncomputable def rightHamiltonian
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightGeneratorDomain →ₗ[ℝ] P.PhysicalHilbert :=
  -T.rightGenerator

@[simp] theorem rightHamiltonian_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    T.rightHamiltonian psi = -T.rightGenerator psi :=
  rfl

/-- The selected right Hamiltonian has its defining signed generator value. -/
theorem rightHamiltonian_hasRightHamiltonianValue
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : T.rightGeneratorDomain) :
    T.HasRightHamiltonianValue psi (T.rightHamiltonian psi) := by
  unfold HasRightHamiltonianValue
  simpa using T.rightGenerator_hasRightGeneratorValue psi

/-- The physical vacuum belongs to the right Hamiltonian domain. -/
theorem vacuum_mem_rightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup) :
    P.vacuum ∈ T.rightGeneratorDomain :=
  T.vacuum_mem_rightGeneratorDomain

/-- The right Hamiltonian annihilates the physical vacuum. -/
@[simp] theorem rightHamiltonian_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.rightHamiltonian
        ⟨P.vacuum, T.vacuum_mem_rightHamiltonianDomain⟩ = 0 := by
  rw [T.rightHamiltonian_apply, T.rightGenerator_vacuum, neg_zero]

/-- Equivalently, the physical vacuum has right Hamiltonian value zero. -/
theorem hasRightHamiltonianValue_vacuum_zero
    (T : P.StronglyContinuousPhysicalSemigroup) :
    T.HasRightHamiltonianValue P.vacuum 0 := by
  unfold HasRightHamiltonianValue
  simpa using T.hasRightGeneratorValue_vacuum_zero

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
