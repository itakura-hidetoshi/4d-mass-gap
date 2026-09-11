import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Set
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 1000000

/-- The common fixed set of a finite family of local/block operators.

This is deliberately the full common fixed set. In the physical application it
is to be identified with the full eigenvalue-one space of the normalized
one-slab transfer; no one-dimensional vacuum hypothesis is built into the
definition. -/
def boundedColorCommonFixedSpace
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) : Set E :=
  {x | ∀ c, P c x = x}

/-- The normalized residual energy of a finite family of local/block operators.

The normalization is by the number of colors/blocks, not by the number of
lattice sites. Thus a fixed finite color type can carry a volume-independent
coercive constant without introducing a spurious `1 / volume` factor. -/
def boundedColorNormalizedResidualEnergy
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E) (x : E) : ℝ :=
  ((Fintype.card C : ℝ)⁻¹) * ∑ c : C, ‖x - P c x‖ ^ 2

/-- The bounded-color residual energy is nonnegative. -/
theorem boundedColorNormalizedResidualEnergy_nonneg
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E) (x : E) :
    0 ≤ boundedColorNormalizedResidualEnergy P x := by
  unfold boundedColorNormalizedResidualEnergy
  positivity

/-- Every vector in the full common fixed set has zero bounded-color residual
energy. -/
theorem boundedColorNormalizedResidualEnergy_eq_zero_of_mem_commonFixedSpace
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E) (x : E)
    (hx : x ∈ boundedColorCommonFixedSpace P) :
    boundedColorNormalizedResidualEnergy P x = 0 := by
  unfold boundedColorNormalizedResidualEnergy
  have hfix : ∀ c : C, P c x = x := hx
  simp [hfix]

/-- Abstract bounded-color reduction.

A frame/Poincare estimate for the normalized local residual energy and a
comparison of that residual energy with a squared transfer defect multiply
without any volume factor. The theorem is intentionally agnostic about the
construction of the local operators: the model-facing work is exactly the two
hypotheses `hframe` and `hcompare`. -/
theorem boundedColorCoercivity_sq_defect_lower_bound
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    (P : C → E →L[ℝ] E)
    (κ η : ℝ)
    (hη0 : 0 ≤ η)
    (defect : E → ℝ)
    (hframe : ∀ x : E,
      κ * ‖x‖ ^ 2 ≤ boundedColorNormalizedResidualEnergy P x)
    (hcompare : ∀ x : E,
      η * boundedColorNormalizedResidualEnergy P x ≤ defect x)
    (x : E) :
    (η * κ) * ‖x‖ ^ 2 ≤ defect x := by
  have hscaled := mul_le_mul_of_nonneg_left (hframe x) hη0
  calc
    (η * κ) * ‖x‖ ^ 2 = η * (κ * ‖x‖ ^ 2) := by ring
    _ ≤ η * boundedColorNormalizedResidualEnergy P x := hscaled
    _ ≤ defect x := hcompare x

section PhysicalOneSlab

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "T" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H N hN beta hbeta
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta

/-- Bounded-color local coercivity plus a raw one-slab comparison gives an
explicit finite-volume transfer gap on the full top-orthogonal sector.

The local family `P` acts on the actual physical Gauss-law Hilbert carrier.
`hframe` is the local/common-fixed-space Poincare obligation and `hcompare` is
the model-facing comparison with the literal raw physical one-slab squared
norm defect. Neither hypothesis singles out a vacuum vector: both are required
on the full canonical top-orthogonal carrier `K`.

If `κ` and `η` can be chosen uniformly over a scaling family while the color
type remains fixed, the coefficient `(η * κ) / 2` is correspondingly uniform.
This theorem itself does not assert that those model estimates hold. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_boundedColorCoercivity_implies_transferGap
    {C : Type*}
    [Fintype C]
    [Nonempty C]
    (P : C → G →L[ℝ] G)
    (κ η : ℝ)
    (hκ0 : 0 ≤ κ)
    (hη0 : 0 ≤ η)
    (hκη1 : η * κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy P (x : G))
    (hcompare : ∀ x : K,
      η * boundedColorNormalizedResidualEnergy P (x : G) * ‖T‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x) :
    (η * κ) / 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hδ0 : 0 ≤ η * κ := mul_nonneg hη0 hκ0
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_rawDefect_lower_bound_implies_transferGap
      H N hN beta hbeta (η * κ) hδ0 hκη1
  intro x
  have hscaled := mul_le_mul_of_nonneg_left (hframe x) hη0
  have hT2 : 0 ≤ ‖T‖ ^ 2 := sq_nonneg ‖T‖
  calc
    (η * κ) * ‖T‖ ^ 2 * ‖(x : G)‖ ^ 2 =
        (η * (κ * ‖(x : G)‖ ^ 2)) * ‖T‖ ^ 2 := by ring
    _ ≤ (η * boundedColorNormalizedResidualEnergy P (x : G)) * ‖T‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hscaled hT2
    _ ≤ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x := hcompare x

/-- A cleaner positive-coefficient form of the bounded-color bridge.

This is the form intended for a scale family: prove fixed-color local coercivity
`κ > 0`, raw comparison `η > 0`, and the harmless normalization bound
`η * κ ≤ 1`; then the actual physical top-orthogonal transfer gap is bounded
below by the explicit positive number `(η * κ) / 2`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_boundedColorCoercivity_positive_transferGap
    {C : Type*}
    [Fintype C]
    [Nonempty C]
    (P : C → G →L[ℝ] G)
    (κ η : ℝ)
    (hκ : 0 < κ)
    (hη : 0 < η)
    (hκη1 : η * κ ≤ 1)
    (hframe : ∀ x : K,
      κ * ‖(x : G)‖ ^ 2 ≤
        boundedColorNormalizedResidualEnergy P (x : G))
    (hcompare : ∀ x : K,
      η * boundedColorNormalizedResidualEnergy P (x : G) * ‖T‖ ^ 2 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
          H N hN beta hbeta x) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
      H N hN beta hbeta := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_boundedColorCoercivity_implies_transferGap
      H N hN beta hbeta P κ η (le_of_lt hκ) (le_of_lt hη) hκη1 hframe hcompare
  have hprod : 0 < η * κ := mul_pos hη hκ
  linarith

end PhysicalOneSlab

end

end MathlibAnalytic
end MGAP4D
