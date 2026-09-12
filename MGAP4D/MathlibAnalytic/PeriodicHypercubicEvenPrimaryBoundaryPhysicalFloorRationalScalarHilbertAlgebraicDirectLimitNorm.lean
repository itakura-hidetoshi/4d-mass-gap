import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimit

/-!
# Norm value on the algebraic direct limit of finite-slot primary scalar OS Hilbert sectors

The preceding layer constructs the algebraic `Module.DirectLimit` of the canonically indexed
finite-slot primary scalar OS Hilbert sectors and proves that every finite-sector canonical map is
injective.  The transition maps are linear isometries, so the Hilbert norm of a representative is
unchanged under every transition.

This file uses Mathlib's canonical linear equivalence from `Module.DirectLimit` to the explicit
generic directed `DirectLimit`, then uses `DirectLimit.lift` to descend representative norms to a
well-defined real-valued function on the algebraic direct limit.  The descended value agrees
exactly with the Hilbert norm on every finite-slot sector, is nonnegative, and vanishes only at the
zero vector.

No `Norm` or `NormedAddCommGroup` instance is installed yet.  In particular, triangle inequality,
scalar homogeneity as direct-limit norm axioms, completion, time translation, semigroup,
Hamiltonian, spectral statements, and mass-gap transfer are deferred to later layers.
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

/-- The explicit generic directed-limit carrier corresponding to the module direct limit from the
preceding layer.  This carrier is used only to apply Mathlib's representative-level `DirectLimit`
API. -/
abbrev fixedSlotHilbertGenericDirectLimit
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) : Type :=
  _root_.DirectLimit
    (fun J : PrimaryScalarFiniteNonnegativeSlotIndex =>
      P.fixedSlotIndexedHilbert J)
    (fun J K hJK => P.fixedSlotIndexedHilbertMap J K hJK)

/-- Mathlib's canonical real-linear equivalence from the module direct limit to the explicit
generic directed-limit quotient. -/
noncomputable def fixedSlotHilbertAlgebraicToGenericLinearEquiv
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.fixedSlotHilbertAlgebraicDirectLimit ≃ₗ[ℝ]
      P.fixedSlotHilbertGenericDirectLimit :=
  Module.DirectLimit.linearEquiv
    (R := ℝ)
    (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
    (G := fun J : PrimaryScalarFiniteNonnegativeSlotIndex =>
      P.fixedSlotIndexedHilbert J)
    (f := fun J K hJK => P.fixedSlotIndexedHilbertMap J K hJK)

/-- The module-to-generic direct-limit equivalence sends a finite-sector canonical vector to its
literal sigma-type representative class. -/
@[simp]
theorem fixedSlotHilbertAlgebraicToGenericLinearEquiv_of
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicToGenericLinearEquiv
        (P.fixedSlotHilbertAlgebraicOf J x) =
      (⟦⟨J, x⟩⟧ : P.fixedSlotHilbertGenericDirectLimit) := by
  simpa [fixedSlotHilbertAlgebraicToGenericLinearEquiv,
    fixedSlotHilbertAlgebraicOf, fixedSlotHilbertAlgebraicDirectLimit,
    fixedSlotHilbertGenericDirectLimit] using
    (Module.DirectLimit.linearEquiv_of
      (R := ℝ)
      (ι := PrimaryScalarFiniteNonnegativeSlotIndex)
      (G := fun M : PrimaryScalarFiniteNonnegativeSlotIndex =>
        P.fixedSlotIndexedHilbert M)
      (f := fun M Q hMQ => P.fixedSlotIndexedHilbertMap M Q hMQ)
      (i := J) (g := x))

/-- Representative Hilbert norms descend to the explicit generic directed limit because every
transition map is an isometry. -/
noncomputable def fixedSlotHilbertGenericNorm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    P.fixedSlotHilbertGenericDirectLimit → ℝ :=
  _root_.DirectLimit.lift
    (fun J K hJK => P.fixedSlotIndexedHilbertMap J K hJK)
    (fun _ x => ‖x‖)
    (by
      intro J K hJK x
      exact (P.fixedSlotIndexedHilbertMap_norm J K hJK x).symm)

/-- On a literal generic direct-limit representative, the descended norm is exactly the Hilbert
norm in that finite-slot sector. -/
@[simp]
theorem fixedSlotHilbertGenericNorm_mk
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertGenericNorm
        (⟦⟨J, x⟩⟧ : P.fixedSlotHilbertGenericDirectLimit) = ‖x‖ := by
  rfl

/-- The canonical norm value on the algebraic module direct limit, obtained by transporting to the
explicit generic direct limit and descending finite-sector Hilbert norms there. -/
noncomputable def fixedSlotHilbertAlgebraicNorm
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) : ℝ :=
  P.fixedSlotHilbertGenericNorm
    (P.fixedSlotHilbertAlgebraicToGenericLinearEquiv z)

/-- Every finite-slot canonical map preserves the descended algebraic norm exactly. -/
@[simp]
theorem fixedSlotHilbertAlgebraicNorm_of
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicNorm
        (P.fixedSlotHilbertAlgebraicOf J x) = ‖x‖ := by
  simp [fixedSlotHilbertAlgebraicNorm]

/-- The descended norm value is unchanged when a finite-sector vector is first moved through any
indexed Hilbert transition. -/
theorem fixedSlotHilbertAlgebraicNorm_of_map
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J K : PrimaryScalarFiniteNonnegativeSlotIndex)
    (hJK : J ≤ K)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicNorm
        (P.fixedSlotHilbertAlgebraicOf K
          (P.fixedSlotIndexedHilbertMap J K hJK x)) =
      P.fixedSlotHilbertAlgebraicNorm
        (P.fixedSlotHilbertAlgebraicOf J x) := by
  rw [P.fixedSlotHilbertAlgebraicNorm_of,
    P.fixedSlotHilbertAlgebraicNorm_of,
    P.fixedSlotIndexedHilbertMap_norm]

/-- The descended algebraic direct-limit norm value is nonnegative. -/
theorem fixedSlotHilbertAlgebraicNorm_nonneg
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    0 ≤ P.fixedSlotHilbertAlgebraicNorm z := by
  obtain ⟨J, x, hx⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [← hx, P.fixedSlotHilbertAlgebraicNorm_of]
  exact norm_nonneg x

/-- The descended norm value is definite: it vanishes exactly at the zero vector of the algebraic
direct limit. -/
theorem fixedSlotHilbertAlgebraicNorm_eq_zero_iff
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    P.fixedSlotHilbertAlgebraicNorm z = 0 ↔ z = 0 := by
  obtain ⟨J, x, hx⟩ := P.fixedSlotHilbertAlgebraic_exists_representation z
  rw [← hx, P.fixedSlotHilbertAlgebraicNorm_of, norm_eq_zero]
  constructor
  · intro hzero
    subst x
    exact map_zero (P.fixedSlotHilbertAlgebraicOf J)
  · intro hzero
    apply P.fixedSlotHilbertAlgebraicOf_injective J
    simpa using hzero

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
