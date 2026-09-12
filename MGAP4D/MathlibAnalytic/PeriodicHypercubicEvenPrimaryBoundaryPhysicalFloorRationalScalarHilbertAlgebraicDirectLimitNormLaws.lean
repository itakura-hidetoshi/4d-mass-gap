import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimitNorm

/-!
# Norm laws on the algebraic direct limit of finite-slot primary scalar OS Hilbert sectors

The preceding layer descends the finite-sector Hilbert norm to a well-defined real-valued
function on the algebraic `Module.DirectLimit`, proves exact preservation on every finite-slot
canonical map, and proves definiteness.

This file proves the remaining representative-level norm laws needed before installing a genuine
normed additive-group structure.  The key point is that Mathlib's `Module.DirectLimit.exists_of₂`
places any two algebraic direct-limit vectors in one common finite-slot Hilbert sector.  Addition
and scalar multiplication can therefore be checked there, where the ordinary Hilbert-space norm
laws already hold.

No metric, `NormedAddCommGroup`, `NormedSpace`, completion, time translation, semigroup,
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
variable {latticeSpacing : ℕ → ℝ}
variable {L :
  PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
    H N hN beta hbeta latticeSpacing}

/-- Any two algebraic direct-limit vectors have representatives in one common finite-slot
Hilbert sector.  This is the directed two-representative form of Mathlib's
`Module.DirectLimit.exists_of₂`. -/
theorem fixedSlotHilbertAlgebraic_exists_common_representation
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    ∃ J : PrimaryScalarFiniteNonnegativeSlotIndex,
      ∃ x y : P.fixedSlotIndexedHilbert J,
        P.fixedSlotHilbertAlgebraicOf J x = z ∧
          P.fixedSlotHilbertAlgebraicOf J y = w := by
  simpa [fixedSlotHilbertAlgebraicDirectLimit, fixedSlotHilbertAlgebraicOf] using
    (Module.DirectLimit.exists_of₂
      (R := ℝ)
      (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
      (G := fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
        P.fixedSlotIndexedHilbert M)
      (f := fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)
      z w)

/-- The descended algebraic norm value vanishes at zero. -/
@[simp]
theorem fixedSlotHilbertAlgebraicNorm_zero
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.fixedSlotHilbertAlgebraicNorm
        (0 : P.fixedSlotHilbertAlgebraicDirectLimit) = 0 := by
  exact (P.fixedSlotHilbertAlgebraicNorm_eq_zero_iff 0).2 rfl

/-- The descended algebraic norm value is invariant under additive negation. -/
@[simp]
theorem fixedSlotHilbertAlgebraicNorm_neg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicNorm (-z) =
      P.fixedSlotHilbertAlgebraicNorm z := by
  obtain ⟨J, x, hx⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [← hx, ← (P.fixedSlotHilbertAlgebraicOf J).map_neg]
  simp only [P.fixedSlotHilbertAlgebraicNorm_of, norm_neg]

/-- Triangle inequality for the descended algebraic norm value.  Both vectors are first represented
in one common finite-slot Hilbert sector, where the usual Hilbert-space triangle inequality
applies. -/
theorem fixedSlotHilbertAlgebraicNorm_add_le
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicNorm (z + w) ≤
      P.fixedSlotHilbertAlgebraicNorm z +
        P.fixedSlotHilbertAlgebraicNorm w := by
  obtain ⟨J, x, y, hx, hy⟩ :=
    P.fixedSlotHilbertAlgebraic_exists_common_representation z w
  rw [← hx, ← hy, ← (P.fixedSlotHilbertAlgebraicOf J).map_add]
  simpa only [P.fixedSlotHilbertAlgebraicNorm_of] using
    (norm_add_le x y)

/-- Exact real scalar homogeneity for the descended algebraic norm value. -/
theorem fixedSlotHilbertAlgebraicNorm_smul
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (c : ℝ)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicNorm (c • z) =
      ‖c‖ * P.fixedSlotHilbertAlgebraicNorm z := by
  obtain ⟨J, x, hx⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [← hx, ← (P.fixedSlotHilbertAlgebraicOf J).map_smul]
  simpa only [P.fixedSlotHilbertAlgebraicNorm_of] using
    (norm_smul c x)

/-- The descended norm of a difference is symmetric under reversing the difference. -/
theorem fixedSlotHilbertAlgebraicNorm_sub_rev
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicNorm (z - w) =
      P.fixedSlotHilbertAlgebraicNorm (w - z) := by
  simpa only [neg_sub] using
    (P.fixedSlotHilbertAlgebraicNorm_neg (z - w)).symm

/-- A difference has zero descended norm exactly when its endpoints coincide. -/
theorem fixedSlotHilbertAlgebraicNorm_sub_eq_zero_iff
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicNorm (z - w) = 0 ↔ z = w := by
  rw [P.fixedSlotHilbertAlgebraicNorm_eq_zero_iff, sub_eq_zero]

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
