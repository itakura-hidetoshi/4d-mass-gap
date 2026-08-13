import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u v

variable {α : Type u} {β : Type v}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Canonical Gram factor of a rectangular real Hilbert--Schmidt kernel.

If `A_K : L²(μ) → L²(ν)` is the rectangular kernel operator, this is the
positive boundary-side operator `A_K† A_K`.  Keeping this construction generic
separates the operator-theoretic Gram identity from any particular Wilson
kernel representative. -/
noncomputable def realL2HilbertSchmidtRectangularKernelFactorizedOperator
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  ((realL2HilbertSchmidtRectangularKernelOperator K)†).comp
    (realL2HilbertSchmidtRectangularKernelOperator K)

/-- Full weak Gram identity for a rectangular Hilbert--Schmidt kernel:
`⟪A_K† A_K f, g⟫ = ⟪A_K f, A_K g⟫`.

This is stronger than the diagonal norm-square identity and is the exact
matrix-coefficient form needed to identify `A†A` with a square Gram-kernel
operator by a subsequent Fubini argument. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f g : Lp ℝ 2 μ) :
    inner ℝ
        (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) g =
      inner ℝ
        (realL2HilbertSchmidtRectangularKernelOperator K f)
        (realL2HilbertSchmidtRectangularKernelOperator K g) := by
  let A := realL2HilbertSchmidtRectangularKernelOperator K
  change inner ℝ ((A†) (A f)) g = inner ℝ (A f) (A g)
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- The weak Gram coefficient can be expressed directly in the original
rectangular Hilbert--Schmidt kernel pairing.  No pointwise representative of
`K` and no square-kernel integrability theorem is needed at this stage. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_eq_pairing
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f g : Lp ℝ 2 μ) :
    inner ℝ
        (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) g =
      realL2HilbertSchmidtKernelPairing K f
        (realL2HilbertSchmidtRectangularKernelOperator K g) := by
  rw [realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner]
  exact realL2HilbertSchmidtRectangularKernelOperator_inner K f
    (realL2HilbertSchmidtRectangularKernelOperator K g)

/-- Diagonal Gram identity: the quadratic form of `A_K† A_K` is the squared
analysis norm. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) :
    inner ℝ
        (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) f =
      ‖realL2HilbertSchmidtRectangularKernelOperator K f‖ ^ 2 := by
  rw [realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner]
  exact real_inner_self_eq_norm_sq _

/-- The generic rectangular Gram factor is symmetric. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_isSymmetric
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ((realL2HilbertSchmidtRectangularKernelFactorizedOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
  intro f g
  calc
    inner ℝ (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) g =
        inner ℝ
          (realL2HilbertSchmidtRectangularKernelOperator K f)
          (realL2HilbertSchmidtRectangularKernelOperator K g) :=
      realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner K f g
    _ = inner ℝ
          (realL2HilbertSchmidtRectangularKernelOperator K g)
          (realL2HilbertSchmidtRectangularKernelOperator K f) := by
      exact real_inner_comm _ _
    _ = inner ℝ
          (realL2HilbertSchmidtRectangularKernelFactorizedOperator K g) f :=
      (realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner K g f).symm
    _ = inner ℝ f
          (realL2HilbertSchmidtRectangularKernelFactorizedOperator K g) := by
      exact real_inner_comm _ _

/-- The generic rectangular Gram factor is positive. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_isPositive
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ((realL2HilbertSchmidtRectangularKernelFactorizedOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsPositive := by
  rw [LinearMap.isPositive_iff]
  refine ⟨realL2HilbertSchmidtRectangularKernelFactorizedOperator_isSymmetric K, ?_⟩
  intro f
  change 0 ≤ inner ℝ
    (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) f
  rw [realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self]
  exact sq_nonneg _

/-- Strict positivity of the Gram quadratic form is equivalent to a nonzero
analysis vector.  This is the cancellation-free nonvanishing criterion that
will be specialized to the completed positive Wilson feature. -/
theorem realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self_pos_iff
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (f : Lp ℝ 2 μ) :
    0 < inner ℝ
        (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) f ↔
      realL2HilbertSchmidtRectangularKernelOperator K f ≠ 0 := by
  rw [realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_self]
  constructor
  · intro hpos hzero
    rw [hzero, norm_zero] at hpos
    norm_num at hpos
  · intro hne
    have hnorm : 0 < ‖realL2HilbertSchmidtRectangularKernelOperator K f‖ :=
      norm_pos_iff.mpr hne
    nlinarith

/-- Audit-visible generic rectangular Gram-factorization receipt. -/
structure RealL2HilbertSchmidtRectangularKernelGramFactorizationPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) : Prop where
  weakGram :
    ∀ f g : Lp ℝ 2 μ,
      inner ℝ
          (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) g =
        inner ℝ
          (realL2HilbertSchmidtRectangularKernelOperator K f)
          (realL2HilbertSchmidtRectangularKernelOperator K g)
  pairingGram :
    ∀ f g : Lp ℝ 2 μ,
      inner ℝ
          (realL2HilbertSchmidtRectangularKernelFactorizedOperator K f) g =
        realL2HilbertSchmidtKernelPairing K f
          (realL2HilbertSchmidtRectangularKernelOperator K g)
  positive :
    ((realL2HilbertSchmidtRectangularKernelFactorizedOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsPositive

/-- Construct the generic rectangular Gram-factorization receipt. -/
theorem realL2HilbertSchmidtRectangularKernelGramFactorizationPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    RealL2HilbertSchmidtRectangularKernelGramFactorizationPackage K :=
  { weakGram := realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner K
    pairingGram :=
      realL2HilbertSchmidtRectangularKernelFactorizedOperator_inner_eq_pairing K
    positive := realL2HilbertSchmidtRectangularKernelFactorizedOperator_isPositive K }

end

end MathlibAnalytic
end MGAP4D
