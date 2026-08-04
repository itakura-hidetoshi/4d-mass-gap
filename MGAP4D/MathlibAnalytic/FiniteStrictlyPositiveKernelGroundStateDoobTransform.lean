import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelPerronOrder
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Proof-relevant data for the ground-state Doob transform of an
operator-norm-normalized finite kernel.  The chosen ground vector is required
to be pointwise strictly positive and fixed by the normalized transfer. -/
structure FiniteKernelGroundStateDoobData
    (α : Type) [Fintype α] where
  kernel : α → α → ℝ
  ground : FiniteBoundaryHilbert α
  ground_pos : FiniteBoundaryPointwisePositive ground
  ground_fixed : finiteKernelNormalizedOperator kernel ground = ground
  kernel_symmetric : ∀ x y : α, kernel x y = kernel y x
  kernel_nonneg : ∀ x y : α, 0 ≤ kernel x y
  raw_ne_zero : finiteKernelOperator kernel ≠ 0

namespace FiniteKernelGroundStateDoobData

variable {α : Type} [Fintype α]

/-- The normalized ground-state Doob kernel.  With the repository's kernel
orientation, `x` is the input coordinate and `y` is the output coordinate. -/
noncomputable def doobKernel
    (D : FiniteKernelGroundStateDoobData α) : α → α → ℝ :=
  fun x y =>
    (‖finiteKernelOperator D.kernel‖⁻¹ * D.kernel x y * D.ground x) /
      D.ground y

/-- The ground-weight multiplication map from ordinary functions into the
ambient Euclidean boundary Hilbert space. -/
noncomputable def weightedVector
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) : FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun x : α => D.ground x * f x

@[simp] theorem weightedVector_apply
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α)
    (x : α) :
    D.weightedVector f x = D.ground x * f x :=
  rfl

/-- Pointwise division by the positive ground state. -/
noncomputable def unweight
    (D : FiniteKernelGroundStateDoobData α)
    (x : FiniteBoundaryHilbert α) : FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun a : α => x a / D.ground a

@[simp] theorem unweight_apply
    (D : FiniteKernelGroundStateDoobData α)
    (x : FiniteBoundaryHilbert α)
    (a : α) :
    D.unweight x a = x a / D.ground a :=
  rfl

/-- Ground multiplication followed by division is the identity. -/
theorem weightedVector_unweight
    (D : FiniteKernelGroundStateDoobData α)
    (x : FiniteBoundaryHilbert α) :
    D.weightedVector (D.unweight x) = x := by
  ext a
  change D.ground a * (x a / D.ground a) = x a
  field_simp [ne_of_gt (D.ground_pos a)]

/-- Division followed by ground multiplication is the identity. -/
theorem unweight_weightedVector
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.unweight (D.weightedVector f) = f := by
  ext a
  change (D.ground a * f a) / D.ground a = f a
  field_simp [ne_of_gt (D.ground_pos a)]

/-- Weighted inner product associated with the Perron ground density
`ground^2`. -/
def weightedInner
    (D : FiniteKernelGroundStateDoobData α)
    (f g : FiniteBoundaryHilbert α) : ℝ :=
  ∑ a : α, D.ground a ^ 2 * f a * g a

/-- Weighted squared norm. -/
def weightedNormSq
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) : ℝ :=
  D.weightedInner f f

/-- Weighted mean against the Perron density. -/
def weightedMean
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) : ℝ :=
  ∑ a : α, D.ground a ^ 2 * f a

/-- Weighted quadratic form of the Doob operator. -/
def weightedDoobQuadratic
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) : ℝ :=
  D.weightedInner (finiteKernelOperator D.doobKernel f) f

/-- Ground multiplication identifies the weighted inner product with the
ambient Euclidean inner product. -/
theorem weightedInner_eq_inner
    (D : FiniteKernelGroundStateDoobData α)
    (f g : FiniteBoundaryHilbert α) :
    D.weightedInner f g = inner ℝ (D.weightedVector f) (D.weightedVector g) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  change D.ground a ^ 2 * f a * g a =
    (D.ground a * g a) * (D.ground a * f a)
  ring

/-- The weighted squared norm is exactly the ordinary norm after ground
multiplication. -/
theorem weightedNormSq_eq_norm_sq
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.weightedNormSq f = ‖D.weightedVector f‖ ^ 2 := by
  rw [weightedNormSq, D.weightedInner_eq_inner]
  exact real_inner_self_eq_norm_sq _

/-- Weighted mean zero is exactly orthogonality of the ground-weighted vector
to the Perron ground vector. -/
theorem weightedMean_eq_inner_ground
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.weightedMean f = inner ℝ (D.weightedVector f) D.ground := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _ha
  change D.ground a ^ 2 * f a = D.ground a * (D.ground a * f a)
  ring

/-- The ground fixed-point equation in pointwise finite-sum form. -/
theorem normalized_kernel_ground_sum
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    ‖finiteKernelOperator D.kernel‖⁻¹ *
        (∑ x : α, D.kernel x y * D.ground x) =
      D.ground y := by
  have hpoint := congrArg
    (fun f : FiniteBoundaryHilbert α => f y) D.ground_fixed
  simpa [finiteKernelNormalizedOperator, finiteKernelOperator_apply] using hpoint

/-- Every row of the ground-state Doob kernel has mass one. -/
theorem doobKernel_sum_eq_one
    (D : FiniteKernelGroundStateDoobData α)
    (y : α) :
    ∑ x : α, D.doobKernel x y = 1 := by
  classical
  calc
    (∑ x : α, D.doobKernel x y) =
        (‖finiteKernelOperator D.kernel‖⁻¹ *
            (∑ x : α, D.kernel x y * D.ground x)) /
          D.ground y := by
      unfold doobKernel
      rw [← Finset.sum_div, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _hx
      ring
    _ = D.ground y / D.ground y := by
      rw [D.normalized_kernel_ground_sum]
    _ = 1 := div_self (ne_of_gt (D.ground_pos y))

/-- The Doob kernel is nonnegative. -/
theorem doobKernel_nonneg
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) :
    0 ≤ D.doobKernel x y := by
  unfold doobKernel
  exact div_nonneg
    (mul_nonneg
      (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (D.kernel_nonneg x y))
      (le_of_lt (D.ground_pos x)))
    (le_of_lt (D.ground_pos y))

/-- Symmetry of the original kernel becomes detailed balance for the Doob
kernel with reversible density `ground^2`. -/
theorem doobKernel_detailedBalance
    (D : FiniteKernelGroundStateDoobData α)
    (x y : α) :
    D.ground y ^ 2 * D.doobKernel x y =
      D.ground x ^ 2 * D.doobKernel y x := by
  unfold doobKernel
  rw [D.kernel_symmetric x y]
  field_simp [ne_of_gt (D.ground_pos x), ne_of_gt (D.ground_pos y)]
  ring

/-- Exact ground-state intertwining: multiplication by the Perron ground
conjugates the Doob operator to the original normalized transfer. -/
theorem weightedVector_doobOperator
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.weightedVector (finiteKernelOperator D.doobKernel f) =
      finiteKernelNormalizedOperator D.kernel (D.weightedVector f) := by
  classical
  ext y
  change
    D.ground y *
        (∑ x : α,
          ((‖finiteKernelOperator D.kernel‖⁻¹ * D.kernel x y *
              D.ground x) / D.ground y) * f x) =
      ‖finiteKernelOperator D.kernel‖⁻¹ *
        (∑ x : α, D.kernel x y * (D.ground x * f x))
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  field_simp [ne_of_gt (D.ground_pos y)]
  ring

/-- The weighted Doob quadratic form is exactly the original normalized
transfer quadratic form after ground multiplication. -/
theorem weightedDoobQuadratic_eq_transfer_inner
    (D : FiniteKernelGroundStateDoobData α)
    (f : FiniteBoundaryHilbert α) :
    D.weightedDoobQuadratic f =
      inner ℝ
        (finiteKernelNormalizedOperator D.kernel (D.weightedVector f))
        (D.weightedVector f) := by
  rw [weightedDoobQuadratic, D.weightedInner_eq_inner,
    D.weightedVector_doobOperator]

/-- A weighted mean-zero Rayleigh estimate for the reversible Doob kernel
transports to the ordinary Perron-orthogonal Rayleigh estimate for the original
normalized transfer. -/
theorem transfer_rayleigh_le_of_weightedDoob
    (D : FiniteKernelGroundStateDoobData α)
    (rate : ℝ)
    (hDoob : ∀ f : FiniteBoundaryHilbert α,
      D.weightedMean f = 0 →
        D.weightedDoobQuadratic f ≤ rate * D.weightedNormSq f)
    (x : FiniteBoundaryHilbert α)
    (hx : inner ℝ x D.ground = 0) :
    inner ℝ (finiteKernelNormalizedOperator D.kernel x) x ≤
      rate * ‖x‖ ^ 2 := by
  let f := D.unweight x
  have hMean : D.weightedMean f = 0 := by
    rw [D.weightedMean_eq_inner_ground, D.weightedVector_unweight]
    exact hx
  have h := hDoob f hMean
  rw [D.weightedDoobQuadratic_eq_transfer_inner,
    D.weightedNormSq_eq_norm_sq, D.weightedVector_unweight] at h
  exact h

/-- Conversely, every Perron-orthogonal Rayleigh estimate for the normalized
transfer gives the corresponding weighted mean-zero estimate for the Doob
kernel. -/
theorem weightedDoob_le_of_transfer_rayleigh
    (D : FiniteKernelGroundStateDoobData α)
    (rate : ℝ)
    (hTransfer : ∀ x : FiniteBoundaryHilbert α,
      inner ℝ x D.ground = 0 →
        inner ℝ (finiteKernelNormalizedOperator D.kernel x) x ≤
          rate * ‖x‖ ^ 2)
    (f : FiniteBoundaryHilbert α)
    (hMean : D.weightedMean f = 0) :
    D.weightedDoobQuadratic f ≤ rate * D.weightedNormSq f := by
  have hOrth : inner ℝ (D.weightedVector f) D.ground = 0 := by
    rw [← D.weightedMean_eq_inner_ground]
    exact hMean
  have h := hTransfer (D.weightedVector f) hOrth
  simpa [D.weightedDoobQuadratic_eq_transfer_inner,
    D.weightedNormSq_eq_norm_sq] using h

/-- Exact equivalence between the normalized-transfer centered Rayleigh bound
and the weighted reversible-Doob centered Rayleigh bound. -/
theorem transfer_rayleigh_iff_weightedDoob
    (D : FiniteKernelGroundStateDoobData α)
    (rate : ℝ) :
    (∀ x : FiniteBoundaryHilbert α,
      inner ℝ x D.ground = 0 →
        inner ℝ (finiteKernelNormalizedOperator D.kernel x) x ≤
          rate * ‖x‖ ^ 2) ↔
    (∀ f : FiniteBoundaryHilbert α,
      D.weightedMean f = 0 →
        D.weightedDoobQuadratic f ≤ rate * D.weightedNormSq f) := by
  constructor
  · exact D.weightedDoob_le_of_transfer_rayleigh rate
  · exact D.transfer_rayleigh_le_of_weightedDoob rate

end FiniteKernelGroundStateDoobData

end

end MathlibAnalytic
end MGAP4D
