import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSRightHamiltonian
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The completed Euclidean-time operators commute.  This is the additive
semigroup law together with commutativity of nonnegative time addition. -/
theorem physicalOperator_commute_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator s
        (T.toPhysicalSemigroup.operator t psi) =
      T.toPhysicalSemigroup.operator t
        (T.toPhysicalSemigroup.operator s psi) := by
  calc
    T.toPhysicalSemigroup.operator s
          (T.toPhysicalSemigroup.operator t psi) =
        ((T.toPhysicalSemigroup.operator s).comp
          (T.toPhysicalSemigroup.operator t)) psi := rfl
    _ = T.toPhysicalSemigroup.operator (s + t) psi := by
      rw [← T.toPhysicalSemigroup.operator_add]
    _ = T.toPhysicalSemigroup.operator (t + s) psi := by
      rw [add_comm]
    _ = ((T.toPhysicalSemigroup.operator t).comp
          (T.toPhysicalSemigroup.operator s)) psi := by
      rw [T.toPhysicalSemigroup.operator_add]
    _ = T.toPhysicalSemigroup.operator t
          (T.toPhysicalSemigroup.operator s psi) := rfl

/-- Right generator difference quotients intertwine the completed physical
semigroup. -/
@[simp] theorem rightDifferenceQuotient_operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.rightDifferenceQuotient
        (T.toPhysicalSemigroup.operator s psi) t =
      T.toPhysicalSemigroup.operator s
        (T.rightDifferenceQuotient psi t) := by
  simp only [rightDifferenceQuotient, map_sub, map_smul]
  rw [T.physicalOperator_commute_apply t s psi]

/-- Applying a physical Euclidean-time operator transports a right generator
value by the same operator. -/
theorem HasRightGeneratorValue.operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi eta : P.PhysicalHilbert}
    (h : T.HasRightGeneratorValue psi eta) (s : NNReal) :
    T.HasRightGeneratorValue
      (T.toPhysicalSemigroup.operator s psi)
      (T.toPhysicalSemigroup.operator s eta) := by
  unfold HasRightGeneratorValue at h ⊢
  have hop :
      Tendsto (T.toPhysicalSemigroup.operator s)
        (nhds eta)
        (nhds (T.toPhysicalSemigroup.operator s eta)) :=
    (T.toPhysicalSemigroup.operator s).continuous.continuousAt
  simpa only [rightDifferenceQuotient_operator] using hop.comp h

/-- The right generator domain is invariant under every completed physical
Euclidean-time operator. -/
theorem physicalOperator_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s : NNReal) {psi : P.PhysicalHilbert}
    (hpsi : psi ∈ T.rightGeneratorDomain) :
    T.toPhysicalSemigroup.operator s psi ∈ T.rightGeneratorDomain := by
  rcases hpsi with ⟨eta, heta⟩
  exact ⟨T.toPhysicalSemigroup.operator s eta, heta.operator T s⟩

/-- The infinitesimal generator commutes with physical Euclidean-time evolution
on its invariant domain. -/
theorem rightGenerator_operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s : NNReal) (psi : T.rightGeneratorDomain) :
    T.rightGenerator
        ⟨T.toPhysicalSemigroup.operator s psi,
          T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩ =
      T.toPhysicalSemigroup.operator s (T.rightGenerator psi) := by
  apply T.hasRightGeneratorValue_unique
    (T.rightGenerator_hasRightGeneratorValue
      ⟨T.toPhysicalSemigroup.operator s psi,
        T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩)
  exact (T.rightGenerator_hasRightGeneratorValue psi).operator T s

/-- Right Hamiltonian difference quotients intertwine the completed physical
semigroup. -/
@[simp] theorem rightHamiltonianDifferenceQuotient_operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s t : NNReal) (psi : P.PhysicalHilbert) :
    T.rightHamiltonianDifferenceQuotient
        (T.toPhysicalSemigroup.operator s psi) t =
      T.toPhysicalSemigroup.operator s
        (T.rightHamiltonianDifferenceQuotient psi t) := by
  simp only [rightHamiltonianDifferenceQuotient, map_sub, map_smul]
  rw [T.physicalOperator_commute_apply t s psi]

/-- Applying physical Euclidean-time evolution transports a right Hamiltonian
value by the same operator. -/
theorem HasRightHamiltonianValue.operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    {psi eta : P.PhysicalHilbert}
    (h : T.HasRightHamiltonianValue psi eta) (s : NNReal) :
    T.HasRightHamiltonianValue
      (T.toPhysicalSemigroup.operator s psi)
      (T.toPhysicalSemigroup.operator s eta) := by
  unfold HasRightHamiltonianValue at h ⊢
  simpa using h.operator T s

/-- The right Hamiltonian commutes with physical Euclidean-time evolution on
its invariant generator domain. -/
theorem rightHamiltonian_operator
    (T : P.StronglyContinuousPhysicalSemigroup)
    (s : NNReal) (psi : T.rightGeneratorDomain) :
    T.rightHamiltonian
        ⟨T.toPhysicalSemigroup.operator s psi,
          T.physicalOperator_mem_rightGeneratorDomain s psi.property⟩ =
      T.toPhysicalSemigroup.operator s (T.rightHamiltonian psi) := by
  rw [T.rightHamiltonian_apply, T.rightGenerator_operator,
    T.rightHamiltonian_apply, map_neg]

/-- The time-evolved vacuum remains in the right Hamiltonian domain. -/
theorem physicalOperator_vacuum_mem_rightHamiltonianDomain
    (T : P.StronglyContinuousPhysicalSemigroup) (s : NNReal) :
    T.toPhysicalSemigroup.operator s P.vacuum ∈ T.rightGeneratorDomain :=
  T.physicalOperator_mem_rightGeneratorDomain s
    T.vacuum_mem_rightHamiltonianDomain

/-- Semigroup covariance specializes consistently to the zero-energy vacuum. -/
@[simp] theorem rightHamiltonian_physicalOperator_vacuum
    (T : P.StronglyContinuousPhysicalSemigroup) (s : NNReal) :
    T.rightHamiltonian
        ⟨T.toPhysicalSemigroup.operator s P.vacuum,
          T.physicalOperator_vacuum_mem_rightHamiltonianDomain s⟩ = 0 := by
  rw [T.rightHamiltonian_operator, T.rightHamiltonian_vacuum, map_zero]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
