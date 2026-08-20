import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularFiniteLaplaceGeneratorDomain
import Mathlib.Tactic

/-!
# Closed-generator identification consequences on the same-root regular OS Hilbert sector

The preceding Laplace-resolvent argument identifies the actual right-generator domain of the
original regular OS `C₀` contraction semigroup with the domain of the nonnegative self-adjoint
graph-closed Hamiltonian `Hbar` and identifies the operator values there.

This file records the operator-level and dynamical consequences of that equality:

* the original right-Hamiltonian partial linear map is exactly `Hbar`;
* hence the original Hamiltonian itself is closed, not merely closable;
* the full closed Hamiltonian domain is invariant under the original OS semigroup;
* `Hbar T_t z = T_t Hbar z` on that full domain;
* every closed-domain orbit has the exact right infinitesimal-generator value
  `-T_t Hbar z` at every nonnegative Euclidean time.

No new analytic hypothesis is introduced; all statements are transported along the proved domain
and operator equality.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

noncomputable section

namespace PrimaryScalarFixedSlotOSPreHilbertData

variable {H : ℕ → ℕ}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing}

/-- Operator-level closure identification: the original OS right Hamiltonian partial linear map is
already its graph closure. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_eq_closedRightHamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian := by
  exact LinearPMap.eq_of_le_of_domain_eq
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed
    (by
      change P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain =
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain
      exact P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_eq_closedRightHamiltonian_domain)

/-- The original OS right Hamiltonian is therefore a closed unbounded operator. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isClosed
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    LinearPMap.IsClosed P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap := by
  rw [P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_eq_closedRightHamiltonian]
  exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isClosed

/-- The original OS semigroup acts on the entire closed Hamiltonian domain. -/
noncomputable def fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z, by
    have hmem :=
      P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant t
        (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z)
    rw [P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_eq_closedRightHamiltonian_domain]
      at hmem
    exact hmem⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    (P.fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate t z :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z :=
  rfl

/-- Full-domain covariance of the graph-closed Hamiltonian under the original same-root OS
semigroup. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate t z) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z) := by
  let x := P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z
  have h :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate_rightGenerator t x
  have hleft :
      P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator
          (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate t x) =
        P.fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate t z := by
    apply Subtype.ext
    rfl
  have hright : P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z := by
    exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_of_closedDomain z
  rw [hleft, hright] at h
  exact h

/-- Every vector in the full closed Hamiltonian domain has the defining actual right-generator
value `-Hbar z`. -/
theorem fixedSlotHilbertDirectLimitRegularClosedDomain_hasRightGeneratorValue
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      (z : P.fixedSlotHilbertDirectLimitRegularSubspace)
      (-P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z) := by
  have h :=
    P.fixedSlotHilbertDirectLimitRegularRightGenerator_hasValue
      (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain z)
  rw [P.fixedSlotHilbertDirectLimitRegularRightGenerator_of_closedDomain z] at h
  simpa only [P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainOfClosedDomain_coe] using h

/-- At every nonnegative Euclidean time, the closed-domain orbit has actual right derivative
`-T_t Hbar z`. -/
theorem fixedSlotHilbertDirectLimitRegularClosedDomain_timeTranslate_hasRightGeneratorValue
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
      (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z)
      (-P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z)) := by
  have h :=
    P.fixedSlotHilbertDirectLimitRegularClosedDomain_hasRightGeneratorValue
      (P.fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate t z)
  rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate] at h
  simpa only [P.fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate_coe] using h

/-- Final closed-generator identification package for the original regular OS semigroup. -/
theorem fixedSlotHilbertDirectLimitRegularClosedGeneratorIdentificationConsequences_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) :
    (P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian) ∧
    LinearPMap.IsClosed P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap ∧
    (∀ (t : NNReal)
      (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain),
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
          (P.fixedSlotHilbertDirectLimitRegularClosedDomainTimeTranslate t z) =
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z)) ∧
    (∀ (t : NNReal)
      (z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain),
      P.FixedSlotHilbertDirectLimitRegularHasRightGeneratorValue
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t z)
        (-P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian z))) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_eq_closedRightHamiltonian,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_isClosed,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate,
    P.fixedSlotHilbertDirectLimitRegularClosedDomain_timeTranslate_hasRightGeneratorValue⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
