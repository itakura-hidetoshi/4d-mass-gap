import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimitNormLaws
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Normed real-space structure on the algebraic primary scalar OS direct limit

The preceding layers construct the algebraic `Module.DirectLimit` of the canonically indexed
finite-slot primary scalar OS Hilbert sectors, descend the finite-sector Hilbert norm to that
carrier, and prove definiteness, symmetry, the triangle inequality, and exact real scalar
homogeneity.

This file packages those already-proved laws into Mathlib's standard analytic hierarchy.  The
canonical metric is

`d(x,y) = N(-x + y)`,

where `N` is the descended algebraic direct-limit norm value.  The normed additive-group and real
normed-space structures then follow without any new analytic assumption.  Finally, every finite
slot Hilbert sector maps into the algebraic direct limit by a genuine Mathlib `LinearIsometry`.

No completion, positive-time closedness assertion, time translation, semigroup, Hamiltonian,
spectral statement, or mass-gap transfer is introduced here.
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

/-- The metric induced by the descended algebraic direct-limit norm value.  Its distance is exactly
`N(-x + y)`, matching Mathlib's additive normed-group convention. -/
noncomputable instance fixedSlotHilbertAlgebraicMetricSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    MetricSpace P.fixedSlotHilbertAlgebraicDirectLimit where
  toPseudoMetricSpace :=
    { dist := fun z w => P.fixedSlotHilbertAlgebraicNorm (-z + w)
      dist_self := fun z => by
        simpa using P.fixedSlotHilbertAlgebraicNorm_zero
      dist_comm := fun z w => by
        rw [neg_add_eq_sub, neg_add_eq_sub]
        exact P.fixedSlotHilbertAlgebraicNorm_sub_rev w z
      dist_triangle := fun z w u => by
        have h :=
          P.fixedSlotHilbertAlgebraicNorm_add_le (-z + w) (-w + u)
        simpa [add_assoc] using h }
  eq_of_dist_eq_zero := by
    intro z w h
    have hzero : -z + w = 0 :=
      (P.fixedSlotHilbertAlgebraicNorm_eq_zero_iff (-z + w)).1 h
    have hwz : w = z := by
      have h' := congrArg (fun t => z + t) hzero
      simpa [add_assoc] using h'
    exact hwz.symm

/-- The algebraic direct limit is a genuine normed additive commutative group with norm equal to the
well-defined descended finite-sector Hilbert norm. -/
noncomputable instance fixedSlotHilbertAlgebraicNormedAddCommGroup
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    NormedAddCommGroup P.fixedSlotHilbertAlgebraicDirectLimit where
  norm := P.fixedSlotHilbertAlgebraicNorm
  dist_eq _ _ := rfl

/-- The installed Mathlib norm is definitionally the descended algebraic direct-limit norm value. -/
@[simp]
theorem fixedSlotHilbertAlgebraic_norm_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z : P.fixedSlotHilbertAlgebraicDirectLimit) :
    ‖z‖ = P.fixedSlotHilbertAlgebraicNorm z :=
  rfl

/-- The installed metric is definitionally the additive norm metric coming from the descended norm. -/
@[simp]
theorem fixedSlotHilbertAlgebraic_dist_eq
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    dist z w = P.fixedSlotHilbertAlgebraicNorm (-z + w) :=
  rfl

/-- Exact scalar homogeneity from the preceding layer equips the algebraic direct limit with its
canonical real `NormedSpace` structure. -/
noncomputable instance fixedSlotHilbertAlgebraicNormedSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    NormedSpace ℝ P.fixedSlotHilbertAlgebraicDirectLimit where
  norm_smul_le c z := by
    change P.fixedSlotHilbertAlgebraicNorm (c • z) ≤
      ‖c‖ * P.fixedSlotHilbertAlgebraicNorm z
    rw [P.fixedSlotHilbertAlgebraicNorm_smul]

/-- Every finite-slot Hilbert sector embeds into the normed algebraic direct limit by a real linear
isometry.  This is the normed-space upgrade of the canonical linear map from the algebraic direct
limit layer. -/
noncomputable def fixedSlotHilbertAlgebraicLinearIsometry
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex) :
    P.fixedSlotIndexedHilbert J →ₗᵢ[ℝ]
      P.fixedSlotHilbertAlgebraicDirectLimit :=
  LinearIsometry.mk
    (P.fixedSlotHilbertAlgebraicOf J)
    (by
      intro x
      change P.fixedSlotHilbertAlgebraicNorm
          (P.fixedSlotHilbertAlgebraicOf J x) = ‖x‖
      exact P.fixedSlotHilbertAlgebraicNorm_of J x)

@[simp]
theorem fixedSlotHilbertAlgebraicLinearIsometry_apply
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x : P.fixedSlotIndexedHilbert J) :
    P.fixedSlotHilbertAlgebraicLinearIsometry J x =
      P.fixedSlotHilbertAlgebraicOf J x :=
  rfl

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
