import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertAlgebraicDirectLimitContraction
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Tactic

/-!
# Factorial OS contraction on the completed Hilbert direct-limit carrier

The preceding layer packages nonnegative rational-time translation on the canonically normed
algebraic direct limit as a continuous linear contraction.  This file takes the canonical Mathlib
uniform completion of that normed real space and extends the contraction uniquely by
`ContinuousLinearMap.completion`.

The extension agrees exactly with the algebraic operator on the dense canonical embedding and
retains

`‖T_t x‖ ≤ ‖x‖`

on the whole completion, hence operator norm at most one.

This layer introduces only the complete normed direct-limit carrier and its rational-time
contractions.  It does not assert a strongly continuous semigroup, a Hamiltonian, a spectral
statement, or a mass-gap transfer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open UniformSpace

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

/-- Canonical completion of the normed algebraic direct limit of finite-slot OS Hilbert sectors. -/
abbrev fixedSlotHilbertDirectLimitCompletion
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L) : Type :=
  Completion P.fixedSlotHilbertAlgebraicDirectLimit

/-- Canonical completion extension of algebraic direct-limit rational-time translation. -/
noncomputable def fixedSlotHilbertDirectLimitTimeTranslateCLM
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.fixedSlotHilbertDirectLimitCompletion →L[ℝ]
      P.fixedSlotHilbertDirectLimitCompletion := by
  change
    Completion P.fixedSlotHilbertAlgebraicDirectLimit →L[ℝ]
      Completion P.fixedSlotHilbertAlgebraicDirectLimit
  exact (P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht).completion

/-- On the dense algebraic direct-limit carrier, the completed operator is exactly the algebraic
rational-time translation. -/
@[simp]
theorem fixedSlotHilbertDirectLimitTimeTranslateCLM_coe
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht
        (z : Completion P.fixedSlotHilbertAlgebraicDirectLimit) =
      (P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht z :
        Completion P.fixedSlotHilbertAlgebraicDirectLimit) := by
  change
    (P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht).completion
        (z : Completion P.fixedSlotHilbertAlgebraicDirectLimit) =
      (P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht z :
        Completion P.fixedSlotHilbertAlgebraicDirectLimit)
  exact ContinuousLinearMap.completion_apply_coe _ _

/-- Rational-time translation remains a contraction after completing the algebraic direct limit. -/
theorem fixedSlotHilbertDirectLimitTimeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (x : P.fixedSlotHilbertDirectLimitCompletion) :
    ‖P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht x‖ ≤ ‖x‖ := by
  change
    ‖(P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht).completion x‖ ≤ ‖x‖
  induction x using Completion.induction_on with
  | hp =>
      exact
        isClosed_le
          (continuous_norm.comp
            (P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht).completion.continuous)
          continuous_norm
  | ih z =>
      rw [ContinuousLinearMap.completion_apply_coe]
      simpa only [Completion.norm_coe,
        P.fixedSlotHilbertAlgebraicTimeTranslateCLM_apply] using
        P.fixedSlotHilbertAlgebraicTimeTranslate_norm_le t ht z

/-- The completed rational-time translation has operator norm at most one. -/
theorem fixedSlotHilbertDirectLimitTimeTranslateCLM_norm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    ‖P.fixedSlotHilbertDirectLimitTimeTranslateCLM t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using P.fixedSlotHilbertDirectLimitTimeTranslate_norm_le t ht x

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
