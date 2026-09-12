import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarHilbertAlgebraicDirectLimitNormedSpace
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Inner-product structure on the algebraic primary scalar OS direct limit

The preceding layers construct the algebraic direct limit of all finite nonnegative rational-slot
primary scalar OS Hilbert sectors, descend the finite-sector Hilbert norm to that direct limit, and
package it as a genuine real normed space.  This file proves that the resulting norm satisfies the
parallelogram identity and then uses Mathlib's `InnerProductSpace.ofNorm` implementation of the
Fréchet–von Neumann–Jordan theorem to install the compatible real inner product.

The parallelogram identity is checked in one common finite-slot Hilbert sector supplied by the
existing directed two-representative theorem.  Thus no new analytic assumption and no hand-written
quotient inner product are introduced.

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

/-- The norm on the algebraic direct limit satisfies the parallelogram identity.  Any two vectors
are represented in one common finite-slot Hilbert sector, where the ordinary Hilbert-space
parallelogram law applies, and the canonical map is a linear isometry. -/
theorem fixedSlotHilbertAlgebraic_parallelogram
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (z w : P.fixedSlotHilbertAlgebraicDirectLimit) :
    ‖z + w‖ * ‖z + w‖ + ‖z - w‖ * ‖z - w‖ =
      2 * (‖z‖ * ‖z‖ + ‖w‖ * ‖w‖) := by
  obtain ⟨J, x, y, hx, hy⟩ :=
    P.fixedSlotHilbertAlgebraic_exists_common_representation z w
  rw [← hx, ← hy,
    ← (P.fixedSlotHilbertAlgebraicOf J).map_add,
    ← (P.fixedSlotHilbertAlgebraicOf J).map_sub]
  change
    ‖P.fixedSlotHilbertAlgebraicLinearIsometry J (x + y)‖ *
        ‖P.fixedSlotHilbertAlgebraicLinearIsometry J (x + y)‖ +
      ‖P.fixedSlotHilbertAlgebraicLinearIsometry J (x - y)‖ *
        ‖P.fixedSlotHilbertAlgebraicLinearIsometry J (x - y)‖ =
      2 *
        (‖P.fixedSlotHilbertAlgebraicLinearIsometry J x‖ *
            ‖P.fixedSlotHilbertAlgebraicLinearIsometry J x‖ +
          ‖P.fixedSlotHilbertAlgebraicLinearIsometry J y‖ *
            ‖P.fixedSlotHilbertAlgebraicLinearIsometry J y‖)
  simpa only [LinearIsometry.norm_map] using
    (parallelogram_law_with_norm_mul ℝ x y)

/-- The algebraic direct limit is a genuine real inner-product space.  Mathlib reconstructs the
inner product canonically from the already-established norm and parallelogram identity. -/
noncomputable instance fixedSlotHilbertAlgebraicInnerProductSpace
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L) :
    InnerProductSpace ℝ P.fixedSlotHilbertAlgebraicDirectLimit :=
  InnerProductSpace.ofNorm ℝ P.fixedSlotHilbertAlgebraic_parallelogram

/-- Every finite-slot canonical linear isometry preserves the reconstructed algebraic direct-limit
inner product exactly. -/
@[simp]
theorem fixedSlotHilbertAlgebraicLinearIsometry_inner
    (P : PrimaryScalarFixedSlotOSPreHilbertData
      H N hN beta hbeta latticeSpacing L)
    (J : PrimaryScalarFiniteNonnegativeSlotIndex)
    (x y : P.fixedSlotIndexedHilbert J) :
    inner ℝ
        (P.fixedSlotHilbertAlgebraicLinearIsometry J x)
        (P.fixedSlotHilbertAlgebraicLinearIsometry J y) =
      inner ℝ x y :=
  (P.fixedSlotHilbertAlgebraicLinearIsometry J).inner_map_map x y

end PrimaryScalarFixedSlotOSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
