import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimitInnerProduct
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Hilbert completion of the all-finite-slot primary scalar OS direct limit

The preceding layers construct the directed algebraic direct limit of all finite nonnegative
rational-slot primary scalar OS Hilbert sectors, equip that direct limit with its canonical normed
real-vector-space structure, and reconstruct the compatible real inner product from the
parallelogram law.

This file now takes the ordinary Mathlib uniform completion of that single same-root algebraic
pre-Hilbert carrier.  The result is a complete real inner-product space.  The algebraic direct
limit embeds densely by Mathlib's canonical completion map, and every finite-slot Hilbert sector
embeds isometrically by composition with its already-canonical algebraic direct-limit isometry.

No positive-time closedness assertion, time translation, semigroup, Hamiltonian, spectral
statement, or mass-gap transfer is introduced here.
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
variable {latticeSpacing : ℕ → ℝ}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta latticeSpacing}

/-- Complete all-finite-slot primary scalar OS Hilbert carrier. -/
def fixedSlotHilbertCompletion
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Type :=
  Completion P.fixedSlotHilbertAlgebraicDirectLimit

noncomputable instance fixedSlotHilbertCompletionNormedAddCommGroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    NormedAddCommGroup P.fixedSlotHilbertCompletion := by
  change NormedAddCommGroup (Completion P.fixedSlotHilbertAlgebraicDirectLimit)
  exact Completion.instNormedAddCommGroup P.fixedSlotHilbertAlgebraicDirectLimit

noncomputable instance fixedSlotHilbertCompletionInnerProductSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    InnerProductSpace ℝ P.fixedSlotHilbertCompletion := by
  change InnerProductSpace ℝ (Completion P.fixedSlotHilbertAlgebraicDirectLimit)
  exact Completion.innerProductSpace

noncomputable instance fixedSlotHilbertCompletionCompleteSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    CompleteSpace P.fixedSlotHilbertCompletion := by
  change CompleteSpace (Completion P.fixedSlotHilbertAlgebraicDirectLimit)
  exact Completion.completeSpace P.fixedSlotHilbertAlgebraicDirectLimit

/-- Canonical dense linear isometry from the algebraic direct limit into its Hilbert completion. -/
noncomputable def fixedSlotHilbertAlgebraicToCompletion
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.fixedSlotHilbertAlgebraicDirectLimit →ₗᵢ[ℝ]
      P.fixedSlotHilbertCompletion := by
  change P.fixedSlotHilbertAlgebraicDirectLimit →ₗᵢ[ℝ]
    Completion P.fixedSlotHilbertAlgebraicDirectLimit
  exact Completion.toComplₗᵢ

@[simp]
theorem fixedSlotHilbertAlgebraicToCompletion_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicToCompletion z =
      (z : Completion P.fixedSlotHilbertAlgebraicDirectLimit) :=
  rfl

/-- The algebraic direct limit is dense in the complete all-finite-slot OS Hilbert carrier. -/
theorem fixedSlotHilbertAlgebraic_dense_in_completion
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    DenseRange (fun z : P.fixedSlotHilbertAlgebraicDirectLimit =>
      P.fixedSlotHilbertAlgebraicToCompletion z) := by
  change DenseRange
    (fun z : P.fixedSlotHilbertAlgebraicDirectLimit =>
      (z : Completion P.fixedSlotHilbertAlgebraicDirectLimit))
  exact Completion.denseRange_coe

/-- Every finite-slot Hilbert sector embeds canonically into the complete all-finite-slot carrier. -/
noncomputable def fixedSlotHilbertCompletionLinearIsometry
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    P.fixedSlotIndexedHilbert J →ₗᵢ[ℝ]
      P.fixedSlotHilbertCompletion := by
  exact
    P.fixedSlotHilbertAlgebraicToCompletion.comp
      (P.fixedSlotHilbertAlgebraicLinearIsometry J)

@[simp]
theorem fixedSlotHilbertCompletionLinearIsometry_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertCompletionLinearIsometry J x =
      (P.fixedSlotHilbertAlgebraicOf J x :
        Completion P.fixedSlotHilbertAlgebraicDirectLimit) :=
  rfl

/-- Finite-slot norms are preserved exactly in the complete all-finite-slot Hilbert carrier. -/
@[simp]
theorem fixedSlotHilbertCompletionLinearIsometry_norm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    ‖P.fixedSlotHilbertCompletionLinearIsometry J x‖ = ‖x‖ :=
  (P.fixedSlotHilbertCompletionLinearIsometry J).norm_map x

/-- Finite-slot inner products are preserved exactly in the complete all-finite-slot Hilbert carrier. -/
@[simp]
theorem fixedSlotHilbertCompletionLinearIsometry_inner
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x y : P.fixedSlotIndexedHilbert J) :
    inner ℝ
        (P.fixedSlotHilbertCompletionLinearIsometry J x)
        (P.fixedSlotHilbertCompletionLinearIsometry J y) =
      inner ℝ x y :=
  (P.fixedSlotHilbertCompletionLinearIsometry J).inner_map_map x y

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
