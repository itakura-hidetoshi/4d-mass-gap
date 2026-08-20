import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularYosidaExponentialContraction
import Mathlib.Tactic

/-!
# Orbitwise Yosida generator convergence on the same-root regular OS core

This file begins the full Yosida semigroup-convergence package by aligning the two generator
realizations that already exist on the canonical regular factorial-OS Hilbert sector.

The original strongly-continuous OS semigroup has its canonical dense right-generator domain and
Hamiltonian `H = -A`.  Its graph closure `H̄` is already self-adjoint and nonnegative, while the
bounded dyadic Yosida Hamiltonians `H_{2^n}` converge strongly to `H̄` on `dom(H̄)`.

Here we prove, without adding assumptions, that:

* the original right-generator domain embeds canonically into `dom(H̄)`;
* `H̄` agrees there exactly with the original OS Hamiltonian;
* the original OS time evolution preserves this embedded domain and `H̄ T_t x = T_t H x`;
* `H_{2^n} T_t x -> T_t H x` for every generator-domain vector and every nonnegative time;
* both `H_{2^n} T_t x` and the corresponding error are uniformly dominated by the original
  graph norm, with the error bounded by `2 ‖H x‖` independently of `n` and `t`.

These are the same-root orbitwise generator estimates used by the subsequent Duhamel comparison.
No spectral functional calculus and no semigroup identification is used here.
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

/-- Canonical embedding of the original right-generator domain into the graph-closed Hamiltonian
domain.  This is inherited from the fact that the original Hamiltonian LinearPMap lies below its
closure. -/
noncomputable def fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
  ⟨(x : P.fixedSlotHilbertDirectLimitRegularSubspace),
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed.1 x.property⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    (P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) = x :=
  rfl

/-- On the original OS generator domain, the graph-closed Hamiltonian is exactly the original
Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_of_rightGenerator
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator x) =
      P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x := by
  exact
    (P.fixedSlotHilbertDirectLimitRegularRightHamiltonianLinearPMap_le_closed.2
      (x := x)
      (y := P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator x) rfl).symm

/-- Dyadic Yosida Hamiltonians converge to the original OS Hamiltonian on the canonical original
generator core. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_on_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)) := by
  have h :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_on_closedDomain
      (P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator x)
  simpa only [P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator_coe,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_of_rightGenerator] using h

/-- Equivalently, the bounded negative Yosida generators converge to the original right generator
on the canonical generator core. -/
theorem fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian_tendsto_on_rightGeneratorDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian n
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop
      (nhds (P.fixedSlotHilbertDirectLimitRegularRightGenerator x)) := by
  have h :=
    (P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_on_rightGeneratorDomain
      x).neg
  simpa only [fixedSlotHilbertDirectLimitRegularNegativeDyadicYosidaHamiltonian,
    ContinuousLinearMap.neg_apply,
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_apply, neg_neg] using h

/-- The original OS semigroup preserves the original right-generator domain, bundled as an actual
domain-valued time translation. -/
noncomputable def fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain :=
  ⟨P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x,
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain_invariant t x⟩

@[simp]
theorem fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate t x :
      P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x :=
  rfl

/-- The original Hamiltonian commutes with the same-root OS semigroup on its canonical domain. -/
theorem fixedSlotHilbertDirectLimitRegularRightHamiltonian_timeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate t x) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x) := by
  simpa only [fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate] using
    P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_endomorphism t x

/-- The graph-closed Hamiltonian therefore agrees with the evolved original Hamiltonian on every
OS translate of an original generator-domain vector. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate_rightGenerator
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian
        (P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator
          (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate t x)) =
      P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x) := by
  rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_of_rightGenerator]
  exact P.fixedSlotHilbertDirectLimitRegularRightHamiltonian_timeTranslate t x

/-- Orbitwise Yosida generator convergence: at every nonnegative Euclidean time, the bounded
Yosida Hamiltonian applied to the OS-evolved core vector converges to the evolved original
Hamiltonian. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_timeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    Tendsto
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x))
      atTop
      (nhds
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x))) := by
  have h :=
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_on_closedDomain
      (P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate t x))
  simpa only [P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator_coe,
    P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate_coe,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate_rightGenerator] using h

/-- Uniform graph-core bound along the whole OS orbit: every dyadic Yosida Hamiltonian is bounded by
the norm of the original Hamiltonian vector, independently of the dyadic index and Euclidean time. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_timeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x)‖ ≤
      ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖ := by
  have hgraph :=
    P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_closedDomain_norm_le
      (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
      (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n)
      (P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator
        (P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate t x))
  have horbit := P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t
    (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
  calc
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
        (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x)‖ ≤
      ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
        (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)‖ := by
      simpa only [fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian,
        P.fixedSlotHilbertDirectLimitRegularClosedDomainOfRightGenerator_coe,
        P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomainTimeTranslate_coe,
        P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_timeTranslate_rightGenerator]
        using hgraph
    _ ≤ ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖ := horbit

/-- Duhamel-ready domination of the orbitwise generator error.  The bound is independent of both
`n` and `t`. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_timeTranslate_error_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) (t : NNReal)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) -
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)‖ ≤
      2 * ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖ := by
  have hleft := P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_timeTranslate_norm_le
    n t x
  have hright := P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism_norm_le t
    (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)
  calc
    ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) -
        P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)‖ ≤
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x)‖ +
        ‖P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
          (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)‖ := norm_sub_le _ _
    _ ≤ ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖ +
        ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖ := add_le_add hleft hright
    _ = 2 * ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖ := by ring

/-- Collected orbitwise generator-convergence package used by the subsequent semigroup comparison. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaOrbitGeneratorConvergence_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularRightGeneratorDomain) :
    (∀ t : NNReal,
      Tendsto
        (fun n : ℕ =>
          P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x))
        atTop
        (nhds
          (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
            (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)))) ∧
    (∀ n : ℕ, ∀ t : NNReal,
      ‖P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian n
            (P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t x) -
          P.fixedSlotHilbertDirectLimitRegularRealTimeEndomorphism t
            (P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x)‖ ≤
        2 * ‖P.fixedSlotHilbertDirectLimitRegularRightHamiltonian x‖) := by
  exact ⟨P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_tendsto_timeTranslate x,
    P.fixedSlotHilbertDirectLimitRegularDyadicYosidaHamiltonian_timeTranslate_error_norm_le x⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
