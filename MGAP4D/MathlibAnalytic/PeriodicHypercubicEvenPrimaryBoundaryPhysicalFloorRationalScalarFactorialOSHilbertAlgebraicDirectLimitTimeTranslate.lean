import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarFactorialOSHilbertTimeTranslateInclusion
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimit
import Mathlib.Tactic

/-!
# Factorial OS rational-time translation on the algebraic Hilbert direct limit

The preceding layer proves that fixed-slot Hilbert time translation commutes exactly with every
canonical finite-slot Hilbert inclusion.  This is precisely the compatibility required by
Mathlib's `Module.DirectLimit.lift` universal property.

This file therefore descends nonnegative rational-time translation from each finite-slot Hilbert
sector to a canonical real-linear endomorphism of the algebraic direct limit.  The construction is
still purely algebraic: no direct-limit norm estimate, completion, strongly continuous semigroup,
Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
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

/-- Translating the canonical datum attached to an index is definitionally the canonical datum
attached to the translated index. -/
@[simp]
theorem fixedSlotDataOfIndex_timeTranslateData
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (t : ℚ) (ht : 0 ≤ t) :
    (P.fixedSlotDataOfIndex J).fixedSlotTimeTranslateData t ht =
      P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J) := by
  rfl

/-- The component map from one finite-slot Hilbert sector into the algebraic direct limit: first
translate the Hilbert vector, then insert it through the canonical map of the translated sector. -/
noncomputable def fixedSlotHilbertAlgebraicTimeTranslateComponent
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    P.fixedSlotIndexedHilbert J →ₗ[ℝ]
      P.fixedSlotHilbertAlgebraicDirectLimit :=
  (P.fixedSlotHilbertAlgebraicOf
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).comp
    ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht).toLinearMap

/-- The component maps respect every directed-system transition.  This is the exact compatibility
hypothesis consumed by `Module.DirectLimit.lift`. -/
theorem fixedSlotHilbertAlgebraicTimeTranslateComponent_map
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicTimeTranslateComponent t ht K
        (P.fixedSlotIndexedHilbertMap J K hJK x) =
      P.fixedSlotHilbertAlgebraicTimeTranslateComponent t ht J x := by
  simp only [fixedSlotHilbertAlgebraicTimeTranslateComponent,
    LinearMap.coe_comp, Function.comp_apply]
  have hnat :
      (P.fixedSlotDataOfIndex
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertInclusion
        (P.fixedSlotDataOfIndex
          (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht K))
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_mono t ht hJK)
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x) =
      (P.fixedSlotDataOfIndex K).fixedSlotHilbertTimeTranslateCLM t ht
        (P.fixedSlotIndexedHilbertMap J K hJK x) := by
    simpa only [fixedSlotDataOfIndex_timeTranslateData,
      fixedSlotIndexedHilbertMap, fixedSlotIndexedHilbertLinearIsometry,
      fixedSlotHilbertInclusion] using
      (P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM_inclusion
        (P.fixedSlotDataOfIndex K) hJK t ht x
  change
    P.fixedSlotHilbertAlgebraicOf
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht K)
        (((P.fixedSlotDataOfIndex K).fixedSlotHilbertTimeTranslateCLM t ht).toLinearMap
          (P.fixedSlotIndexedHilbertMap J K hJK x)) =
      P.fixedSlotHilbertAlgebraicOf
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)
        (((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht).toLinearMap x)
  change
    (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)).fixedSlotHilbertInclusion
      (P.fixedSlotDataOfIndex
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht K))
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_mono t ht hJK)
      (((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht).toLinearMap x) =
    ((P.fixedSlotDataOfIndex K).fixedSlotHilbertTimeTranslateCLM t ht).toLinearMap
      (P.fixedSlotIndexedHilbertMap J K hJK x) at hnat
  rw [← hnat]
  simpa only [fixedSlotIndexedHilbertMap, fixedSlotIndexedHilbertLinearIsometry,
    fixedSlotHilbertInclusion] using
    P.fixedSlotHilbertAlgebraicOf_map
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht K)
      (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate_mono t ht hJK)
      (((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht).toLinearMap x)

/-- Canonical nonnegative-rational time translation on the algebraic direct limit of finite-slot
primary-scalar OS Hilbert sectors. -/
noncomputable def fixedSlotHilbertAlgebraicTimeTranslate
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t) :
    P.fixedSlotHilbertAlgebraicDirectLimit →ₗ[ℝ]
      P.fixedSlotHilbertAlgebraicDirectLimit :=
  Module.DirectLimit.lift
    ℝ PrimaryScalarFiniteNonnegativeSlotIndex
    (fun J : PrimaryScalarFiniteNonnegativeSlotIndex => P.fixedSlotIndexedHilbert J)
    (fun J K hJK => P.fixedSlotIndexedHilbertMap J K hJK)
    (fun J => P.fixedSlotHilbertAlgebraicTimeTranslateComponent t ht J)
    (fun J K hJK x =>
      P.fixedSlotHilbertAlgebraicTimeTranslateComponent_map t ht J K hJK x)

/-- On every canonical finite-slot representative, algebraic direct-limit time translation is
exactly fixed-slot Hilbert translation followed by insertion of the translated slot sector. -/
@[simp]
theorem fixedSlotHilbertAlgebraicTimeTranslate_of
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing L)
    (t : ℚ) (ht : 0 ≤ t)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicTimeTranslate t ht
        (P.fixedSlotHilbertAlgebraicOf J x) =
      P.fixedSlotHilbertAlgebraicOf
        (primaryScalarFiniteNonnegativeSlotIndexTimeTranslate t ht J)
        ((P.fixedSlotDataOfIndex J).fixedSlotHilbertTimeTranslateCLM t ht x) := by
  change
    P.fixedSlotHilbertAlgebraicTimeTranslate t ht
        (P.fixedSlotHilbertAlgebraicOf J x) =
      P.fixedSlotHilbertAlgebraicTimeTranslateComponent t ht J x
  simpa only [fixedSlotHilbertAlgebraicTimeTranslate, fixedSlotHilbertAlgebraicOf] using
    (Module.DirectLimit.lift_of
      (R := ℝ)
      (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
      (G := fun K : PrimaryScalarFiniteNonnegativeSlotIndex => P.fixedSlotIndexedHilbert K)
      (f := fun K M hKM => P.fixedSlotIndexedHilbertMap K M hKM)
      (g := fun K => P.fixedSlotHilbertAlgebraicTimeTranslateComponent t ht K)
      (Hg := fun K M hKM y =>
        P.fixedSlotHilbertAlgebraicTimeTranslateComponent_map t ht K M hKM y)
      x)

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
