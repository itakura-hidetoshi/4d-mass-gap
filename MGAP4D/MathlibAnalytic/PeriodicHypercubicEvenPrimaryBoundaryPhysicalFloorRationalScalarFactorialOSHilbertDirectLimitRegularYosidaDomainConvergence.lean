import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularPositiveResolventYosida
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# Yosida approximation on the closed same-root regular OS Hamiltonian domain

For the canonical nonnegative self-adjoint regular Hamiltonian `H̄`, the bounded positive resolvent
and normalized Yosida contraction from the preceding layer satisfy the exact domain identity

`x - J_λ x = R_λ (H̄ x)`.

Consequently

`‖x - J_λ x‖ ≤ λ⁻¹ ‖H̄ x‖`

for every `x ∈ dom(H̄)`.  Along the canonical dyadic scale `λₙ = 2ⁿ` this yields strong convergence
`J_{λₙ} x → x` on the closed Hamiltonian domain.  We also package the bounded Yosida Hamiltonian

`H_λ = λ (I - J_λ)`

and prove `H_λ x = J_λ (H̄ x)` on `dom(H̄)`, hence the uniform graph-core estimate
`‖H_λ x‖ ≤ ‖H̄ x‖`.

No spectral functional calculus or exponential-semigroup identity is used.
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

/-- The positive resolvent is also a left inverse of the positive Hamiltonian shift. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_closedShift
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x) =
      (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  have hdomain :
      P.fixedSlotHilbertDirectLimitRegularPositiveResolventDomain lambda hlambda
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x) = x := by
    apply P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_injective hlambda
    exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_positiveResolventDomain
      lambda hlambda
      (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x)
  rw [P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_apply]
  exact congrArg
    (fun z : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain =>
      (z : P.fixedSlotHilbertDirectLimitRegularSubspace)) hdomain

/-- Exact Yosida defect identity on the closed Hamiltonian domain. -/
theorem fixedSlotHilbertDirectLimitRegular_sub_yosidaResolvent_eq_positiveResolvent_hamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
        P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x) := by
  have hshift := P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_closedShift
    lambda hlambda x
  rw [P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply,
    map_add, map_smul] at hshift
  rw [P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_apply]
  calc
    (x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
        lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      (lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) +
        P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
          (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)) -
        lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
      rw [hshift]
    _ = P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x) := by
      module

/-- Sharp graph-core error estimate for the normalized Yosida resolvent. -/
theorem fixedSlotHilbertDirectLimitRegular_sub_yosidaResolvent_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
        P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ ≤
      lambda⁻¹ * ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x‖ := by
  rw [P.fixedSlotHilbertDirectLimitRegular_sub_yosidaResolvent_eq_positiveResolvent_hamiltonian]
  exact P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_norm_bound lambda hlambda
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)

/-- Canonical dyadic Yosida scale `λₙ = 2ⁿ`. -/
noncomputable def fixedSlotHilbertDirectLimitRegularYosidaDyadicScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n

theorem fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos (n : ℕ) :
    0 < fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n := by
  unfold fixedSlotHilbertDirectLimitRegularYosidaDyadicScale
  positivity

/-- The inverse dyadic scale tends to zero. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_inv_tendsto_zero :
    Tendsto
      (fun n : ℕ => (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)⁻¹)
      atTop (nhds 0) := by
  have hnonneg : 0 ≤ ((2 : ℝ)⁻¹) := by positivity
  have hlt : (2 : ℝ)⁻¹ < 1 := by norm_num
  have hpow : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt
  simpa [fixedSlotHilbertDirectLimitRegularYosidaDyadicScale, inv_pow] using hpow

/-- Dyadic normalized Yosida resolvent. -/
noncomputable def fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (n : ℕ) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  P.fixedSlotHilbertDirectLimitRegularYosidaResolvent
    (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
    (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n)

/-- On `dom(H̄)`, dyadic Yosida resolvents converge strongly to the identity. -/
theorem fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto_on_closedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop (nhds (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
  have herror : Tendsto
      (fun n : ℕ =>
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
          P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
            (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop (nhds 0) := by
    apply squeeze_zero_norm
      (a := fun n : ℕ =>
        (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)⁻¹ *
          ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x‖)
    · intro n
      exact P.fixedSlotHilbertDirectLimitRegular_sub_yosidaResolvent_norm_le
        (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale n)
        (fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_pos n) x
    · simpa only [zero_mul] using
        fixedSlotHilbertDirectLimitRegularYosidaDyadicScale_inv_tendsto_zero.mul_const
          ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x‖
  have hxconst : Tendsto
      (fun _ : ℕ => (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) atTop
      (nhds (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) := tendsto_const_nhds
  have hrecover : Tendsto
      (fun n : ℕ =>
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
          ((x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
            P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
              (x : P.fixedSlotHilbertDirectLimitRegularSubspace)))
      atTop
      (nhds ((x : P.fixedSlotHilbertDirectLimitRegularSubspace) - 0)) :=
    hxconst.sub herror
  have hrecoverFunction :
      (fun n : ℕ =>
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
          ((x : P.fixedSlotHilbertDirectLimitRegularSubspace) -
            P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
              (x : P.fixedSlotHilbertDirectLimitRegularSubspace))) =
      (fun n : ℕ =>
        P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
          (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) := by
    funext n
    abel
  rw [hrecoverFunction] at hrecover
  simpa only [sub_zero] using hrecover

/-- Bounded Yosida Hamiltonian `H_λ = λ (I - J_λ)`. -/
noncomputable def fixedSlotHilbertDirectLimitRegularYosidaHamiltonian
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  lambda •
    (ContinuousLinearMap.id ℝ P.fixedSlotHilbertDirectLimitRegularSubspace -
      P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda)

@[simp] theorem fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian lambda hlambda y =
      lambda •
        (y - P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda y) := by
  simp [fixedSlotHilbertDirectLimitRegularYosidaHamiltonian]

/-- On the closed domain, the bounded Yosida Hamiltonian is `J_λ H̄`. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_closedDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian lambda hlambda
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) =
      P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda
        (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x) := by
  rw [P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_apply,
    P.fixedSlotHilbertDirectLimitRegular_sub_yosidaResolvent_eq_positiveResolvent_hamiltonian,
    P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_apply]

/-- Uniform graph-core norm estimate for bounded Yosida Hamiltonians. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_closedDomain_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    ‖P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian lambda hlambda
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ ≤
      ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x‖ := by
  rw [P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_closedDomain]
  exact P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_norm_bound lambda hlambda
    (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)

/-- Domain-level Yosida approximation package. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaDomain_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    Tendsto
      (fun n : ℕ => P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent n
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace))
      atTop (nhds (x : P.fixedSlotHilbertDirectLimitRegularSubspace)) ∧
      (∀ (lambda : ℝ) (hlambda : 0 < lambda),
        ‖P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian lambda hlambda
            (x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ ≤
          ‖P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x‖) := by
  refine ⟨P.fixedSlotHilbertDirectLimitRegularDyadicYosidaResolvent_tendsto_on_closedDomain x, ?_⟩
  intro lambda hlambda
  exact P.fixedSlotHilbertDirectLimitRegularYosidaHamiltonian_closedDomain_norm_le lambda hlambda x

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
