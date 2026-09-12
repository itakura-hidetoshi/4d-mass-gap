import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertAlgebraicDirectLimitTimeTranslate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimitNormedSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic

/-!
# Factorial OS contraction on the normed algebraic Hilbert direct limit

The preceding layer descends nonnegative rational-time translation to a canonical real-linear
endomorphism of the algebraic direct limit of finite-slot primary scalar OS Hilbert sectors.  The
algebraic direct limit already carries its canonical Mathlib normed real-space structure, and every
finite-slot Hilbert sector embeds into it by a linear isometry.

This file combines those two same-root constructions.  Every algebraic direct-limit vector has a
finite-slot representative; on such a representative, the descended time translation is exactly
the fixed-slot Hilbert contraction followed by the canonical translated-sector insertion.  Since
both canonical insertions are linear isometries, the finite-sector contraction estimate gives

`‖T_t z‖ ≤ ‖z‖`

for every algebraic direct-limit vector.  The descended linear map is then packaged with Mathlib
`LinearMap.mkContinuous` at bound `1`, and its operator norm is recorded to be at most one.

No completion of the algebraic direct limit, strongly continuous semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

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

/-- The descended nonnegative-rational time translation is a contraction for the canonical norm on
the algebraic direct limit. -/
theorem fixedSlotHilbertAlgebraicTimeTranslate_norm_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    ‖P.fixedSlotHilbertAlgebraicTimeTranslate t ht z‖ ≤ ‖z‖ := by
  obtain ⟨J, x, rfl⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [P.fixedSlotHilbertAlgebraicTimeTranslate_of]
  change
    ‖P.fixedSlotHilbertAlgebraicLinearIsometry
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x)‖ ≤
      ‖P.fixedSlotHilbertAlgebraicLinearIsometry J x‖
  rw [
    (P.fixedSlotHilbertAlgebraicLinearIsometry
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).norm_map,
    (P.fixedSlotHilbertAlgebraicLinearIsometry J).norm_map]
  exact
    (P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslate_norm_le t ht x

/-- Continuous-linear packaging of algebraic direct-limit rational-time translation, with the
sharp contraction bound `1` inherited from the finite-slot Hilbert contractions. -/
noncomputable def fixedSlotHilbertAlgebraicTimeTranslateCLM
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.fixedSlotHilbertAlgebraicDirectLimit →L[ℝ]
      P.fixedSlotHilbertAlgebraicDirectLimit :=
  (P.fixedSlotHilbertAlgebraicTimeTranslate t ht).mkContinuous 1 fun z => by
    simpa using P.fixedSlotHilbertAlgebraicTimeTranslate_norm_le t ht z

@[simp]
theorem fixedSlotHilbertAlgebraicTimeTranslateCLM_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht z =
      P.fixedSlotHilbertAlgebraicTimeTranslate t ht z :=
  rfl

/-- The continuous-linear algebraic direct-limit time translation has operator norm at most one. -/
theorem fixedSlotHilbertAlgebraicTimeTranslateCLM_norm_le_one
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    ‖P.fixedSlotHilbertAlgebraicTimeTranslateCLM t ht‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa using P.fixedSlotHilbertAlgebraicTimeTranslate_norm_le t ht z

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
