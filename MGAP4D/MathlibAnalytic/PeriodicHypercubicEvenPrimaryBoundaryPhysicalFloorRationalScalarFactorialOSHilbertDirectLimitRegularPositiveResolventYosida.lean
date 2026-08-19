import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertDirectLimitRegularSelfAdjointHamiltonian
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventIdentity
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-!
# Bounded positive resolvent and Yosida contraction on the same-root regular OS Hilbert sector

The graph-closed regular Hamiltonian is self-adjoint and nonnegative.  Specializing the generic
`LinearPMap.realResolvent` machinery to Rayleigh threshold `0` and real spectral parameter `-λ`
therefore produces the positive resolvent

`R_λ = (λ I + H̄)⁻¹`, `λ > 0`,

as a continuous linear endomorphism of the complete regular Hilbert space.  The sharp contraction
estimates

`‖R_λ‖ ≤ λ⁻¹`,  `‖λ R_λ‖ ≤ 1`

and the positive resolvent identity are inherited without adding any analytic hypothesis.  The
normalized maps `J_λ = λ R_λ` are the bounded Yosida resolvent contractions used by the next
semigroup-identification layer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Set Filter Topology
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

/-- The nonnegative closed Hamiltonian has Rayleigh threshold zero in the generic resolvent API. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    0 * ‖(x : P.fixedSlotHilbertDirectLimitRegularSubspace)‖ ^ 2 ≤
      inner ℝ (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian x)
        (x : P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  simpa using P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_inner_nonneg x

/-- The bounded positive resolvent `R_λ = (λ I + H̄)⁻¹` on the same-root regular Hilbert sector. -/
noncomputable def fixedSlotHilbertDirectLimitRegularPositiveResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  LinearPMap.realResolvent
    (A := P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian)
    (mass := (0 : ℝ)) (lambda := -lambda)
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
    (neg_lt_zero.mpr hlambda)
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound

/-- Domain-valued positive resolvent preimage. -/
noncomputable def fixedSlotHilbertDirectLimitRegularPositiveResolventDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain :=
  (P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realShiftLinearEquiv
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
    (mass := (0 : ℝ)) (lambda := -lambda)
    (neg_lt_zero.mpr hlambda)
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound).symm y

@[simp] theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda y =
      (P.fixedSlotHilbertDirectLimitRegularPositiveResolventDomain lambda hlambda y :
        P.fixedSlotHilbertDirectLimitRegularSubspace) := by
  rfl

/-- The generic real shift at `-λ` is exactly the positive Hamiltonian shift `λI + H̄`. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_realShift_neg_eq_positiveShift
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ)
    (x : P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.domain) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realShift (-lambda) x =
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda x := by
  rw [LinearPMap.realShift_apply,
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_apply]
  module

/-- The domain-valued positive resolvent is a right inverse of `λI + H̄`. -/
theorem fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift_positiveResolventDomain
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonianShift lambda
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolventDomain lambda hlambda y) = y := by
  rw [← P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_realShift_neg_eq_positiveShift]
  unfold fixedSlotHilbertDirectLimitRegularPositiveResolventDomain
  exact P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realShift_realResolvent_preimage
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
    (mass := (0 : ℝ)) (lambda := -lambda)
    (neg_lt_zero.mpr hlambda)
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound y

/-- Sharp pointwise positive-resolvent estimate. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_norm_bound
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda y‖ ≤
      lambda⁻¹ * ‖y‖ := by
  simpa [fixedSlotHilbertDirectLimitRegularPositiveResolvent] using
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realResolventLinearMap_norm_bound
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
      (mass := (0 : ℝ)) (lambda := -lambda)
      (neg_lt_zero.mpr hlambda)
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound y

/-- Sharp operator-norm positive-resolvent estimate. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda‖ ≤ lambda⁻¹ := by
  simpa [fixedSlotHilbertDirectLimitRegularPositiveResolvent] using
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realResolvent_norm_le
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
      (mass := (0 : ℝ)) (lambda := -lambda)
      (neg_lt_zero.mpr hlambda)
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound

/-- Positive-resolvent identity in the standard `λI + H̄` parametrization. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_identity
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda -
        P.fixedSlotHilbertDirectLimitRegularPositiveResolvent mu hmu =
      (mu - lambda) •
        ((P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda).comp
          (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent mu hmu)) := by
  have hscalar : -lambda + mu = mu - lambda := by ring
  simpa [fixedSlotHilbertDirectLimitRegularPositiveResolvent, hscalar] using
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realResolvent_sub_eq_smul_comp
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
      (mass := (0 : ℝ)) (lambda := -lambda) (mu := -mu)
      (neg_lt_zero.mpr hlambda) (neg_lt_zero.mpr hmu)
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound

/-- Quantitative two-parameter norm control for the positive resolvent. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolvent_sub_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda -
        P.fixedSlotHilbertDirectLimitRegularPositiveResolvent mu hmu‖ ≤
      |mu - lambda| * (lambda⁻¹ * mu⁻¹) := by
  have h :=
    P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian.realResolvent_sub_norm_le
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_isSelfAdjoint
      (mass := (0 : ℝ)) (lambda := -lambda) (mu := -mu)
      (neg_lt_zero.mpr hlambda) (neg_lt_zero.mpr hmu)
      P.fixedSlotHilbertDirectLimitRegularClosedRightHamiltonian_zero_rayleigh_lower_bound
  have hscalar : -lambda + mu = mu - lambda := by ring
  simpa [fixedSlotHilbertDirectLimitRegularPositiveResolvent, hscalar] using h

/-- Normalized Yosida resolvent `J_λ = λ(λI + H̄)⁻¹`. -/
noncomputable def fixedSlotHilbertDirectLimitRegularYosidaResolvent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    P.fixedSlotHilbertDirectLimitRegularSubspace →L[ℝ]
      P.fixedSlotHilbertDirectLimitRegularSubspace :=
  lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda

@[simp] theorem fixedSlotHilbertDirectLimitRegularYosidaResolvent_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda y =
      lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda y := by
  rfl

/-- Every normalized Yosida resolvent is a contraction. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaResolvent_norm_bound
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda)
    (y : P.fixedSlotHilbertDirectLimitRegularSubspace) :
    ‖P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda y‖ ≤ ‖y‖ := by
  rw [P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_apply, norm_smul, Real.norm_eq_abs,
    abs_of_pos hlambda]
  have hres := P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_norm_bound lambda hlambda y
  have hinv : lambda * lambda⁻¹ = 1 := by
    exact mul_inv_cancel₀ (ne_of_gt hlambda)
  calc
    lambda * ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda y‖ ≤
        lambda * (lambda⁻¹ * ‖y‖) := mul_le_mul_of_nonneg_left hres hlambda.le
    _ = ‖y‖ := by rw [← mul_assoc, hinv, one_mul]

/-- Operator norm of every normalized Yosida resolvent is at most one. -/
theorem fixedSlotHilbertDirectLimitRegularYosidaResolvent_norm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ‖P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda‖ ≤ 1 := by
  unfold fixedSlotHilbertDirectLimitRegularYosidaResolvent
  have hres := P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_norm_le lambda hlambda
  calc
    ‖lambda • P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda‖ ≤
        ‖lambda‖ * ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda‖ :=
      ContinuousLinearMap.opNorm_smul_le lambda
        (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda)
    _ = lambda * ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda‖ := by
      rw [Real.norm_eq_abs, abs_of_pos hlambda]
    _ ≤ lambda * lambda⁻¹ := mul_le_mul_of_nonneg_left hres hlambda.le
    _ = 1 := by exact mul_inv_cancel₀ (ne_of_gt hlambda)

/-- Bounded positive-resolvent/Yosida package. -/
theorem fixedSlotHilbertDirectLimitRegularPositiveResolventYosida_package
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    ‖P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda‖ ≤ lambda⁻¹ ∧
      ‖P.fixedSlotHilbertDirectLimitRegularYosidaResolvent lambda hlambda‖ ≤ 1 ∧
      P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda -
          P.fixedSlotHilbertDirectLimitRegularPositiveResolvent mu hmu =
        (mu - lambda) •
          ((P.fixedSlotHilbertDirectLimitRegularPositiveResolvent lambda hlambda).comp
            (P.fixedSlotHilbertDirectLimitRegularPositiveResolvent mu hmu)) :=
  ⟨P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_norm_le lambda hlambda,
    P.fixedSlotHilbertDirectLimitRegularYosidaResolvent_norm_le_one lambda hlambda,
    P.fixedSlotHilbertDirectLimitRegularPositiveResolvent_identity lambda mu hlambda hmu⟩

end PrimaryScalarFixedSlotOSPreHilbertData

end
end MathlibAnalytic
end MGAP4D
