import MGAP4D.MathlibAnalytic.FiniteContinuousKernelOperatorPerronEigenvalue
import MGAP4D.MathlibAnalytic.FiniteContinuousNonsingularMatrixInverse
import MGAP4D.MathlibAnalytic.FiniteStrictlyPositiveKernelPerronFixedSpace
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- The constant-one matrix on a finite carrier. -/
noncomputable def finiteAllOnesMatrix
    {α : Type}
    [Fintype α] : Matrix α α ℝ :=
  fun _ _ => 1

/-- The constant-one vector in the finite Euclidean boundary Hilbert space. -/
noncomputable def finiteBoundaryOneVector
    {α : Type}
    [Fintype α] : FiniteBoundaryHilbert α :=
  WithLp.toLp 2 fun _ : α => 1

@[simp] theorem finiteBoundaryOneVector_apply
    {α : Type}
    [Fintype α]
    (x : α) :
    finiteBoundaryOneVector (α := α) x = 1 :=
  rfl

/-- Matrix of the operator-norm-normalized finite kernel, with rows indexed by
output configurations and columns by input configurations. -/
noncomputable def finiteKernelNormalizedMatrix
    {α : Type}
    [Fintype α]
    (kernel : α → α → ℝ) : Matrix α α ℝ :=
  fun output input =>
    ‖finiteKernelOperator kernel‖⁻¹ * kernel input output

/-- The normalized matrix acts on ordinary coordinate functions exactly as the
normalized finite-kernel transfer acts on the corresponding Euclidean vector. -/
theorem finiteKernelNormalizedMatrix_mulVec_apply
    {α : Type}
    [Fintype α]
    (kernel : α → α → ℝ)
    (v : α → ℝ)
    (output : α) :
    Matrix.mulVec (finiteKernelNormalizedMatrix kernel) v output =
      finiteKernelNormalizedOperator kernel (WithLp.toLp 2 v) output := by
  change
    (∑ input : α,
      (‖finiteKernelOperator kernel‖⁻¹ * kernel input output) * v input) =
      ‖finiteKernelOperator kernel‖⁻¹ *
        ∑ input : α, kernel input output * v input
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro input _hInput
  ring

/-- The rank-one anchored Perron matrix `I - T + J`, where `J` is the
constant-one matrix. -/
noncomputable def finiteKernelPerronAnchorMatrix
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    (kernel : α → α → ℝ) : Matrix α α ℝ :=
  fun output input =>
    (if output = input then 1 else 0) -
      finiteKernelNormalizedMatrix kernel output input + 1

/-- Pointwise action of the anchored matrix. -/
theorem finiteKernelPerronAnchorMatrix_mulVec_apply
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    (kernel : α → α → ℝ)
    (v : α → ℝ)
    (output : α) :
    Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel) v output =
      v output -
        finiteKernelNormalizedOperator kernel (WithLp.toLp 2 v) output +
        ∑ input : α, v input := by
  classical
  unfold finiteKernelPerronAnchorMatrix
  change
    (∑ input : α,
      (((if output = input then 1 else 0) -
          finiteKernelNormalizedMatrix kernel output input + 1) * v input)) = _
  calc
    (∑ input : α,
      (((if output = input then 1 else 0) -
          finiteKernelNormalizedMatrix kernel output input + 1) * v input)) =
        (∑ input : α,
          (if output = input then 1 else 0) * v input) -
          Matrix.mulVec (finiteKernelNormalizedMatrix kernel) v output +
          ∑ input : α, v input := by
            rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro input _hInput
            ring
    _ = v output -
          Matrix.mulVec (finiteKernelNormalizedMatrix kernel) v output +
          ∑ input : α, v input := by
            simp [eq_comm]
    _ = v output -
          finiteKernelNormalizedOperator kernel (WithLp.toLp 2 v) output +
          ∑ input : α, v input := by
            rw [finiteKernelNormalizedMatrix_mulVec_apply]

/-- A pointwise continuous normalized finite-kernel family gives a continuous
normalized matrix family. -/
theorem continuous_finiteKernelNormalizedMatrix
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ input output : α,
      Continuous (fun x => kernel x input output))
    (hraw : ∀ x, finiteKernelOperator (kernel x) ≠ 0) :
    Continuous (fun x => finiteKernelNormalizedMatrix (kernel x)) := by
  apply continuous_pi
  intro output
  apply continuous_pi
  intro input
  exact
    ((continuous_finiteKernelOperator_norm kernel hkernel).inv₀
      (fun x => norm_ne_zero_iff.mpr (hraw x))).mul
        (hkernel input output)

/-- The anchored Perron matrix varies continuously with a continuously
normalized finite-kernel family. -/
theorem continuous_finiteKernelPerronAnchorMatrix
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    [DecidableEq α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ input output : α,
      Continuous (fun x => kernel x input output))
    (hraw : ∀ x, finiteKernelOperator (kernel x) ≠ 0) :
    Continuous (fun x => finiteKernelPerronAnchorMatrix (kernel x)) := by
  apply continuous_pi
  intro output
  apply continuous_pi
  intro input
  exact
    (continuous_const.sub
      ((continuous_finiteKernelNormalizedMatrix kernel hkernel hraw).apply
        output input)).add continuous_const

/-- A pointwise strictly-positive finite vector has strictly-positive total
coordinate mass. -/
theorem finiteBoundaryCoordinateSum_pos
    {α : Type}
    [Fintype α]
    [Nonempty α]
    (p : FiniteBoundaryHilbert α)
    (hp : FiniteBoundaryPointwisePositive p) :
    0 < ∑ x : α, p x := by
  classical
  apply Finset.sum_pos'
  · intro x _hx
    exact le_of_lt (hp x)
  · let x : α := Classical.choice inferInstance
    exact ⟨x, Finset.mem_univ x, hp x⟩

/-- Inner product of the constant-one vector with a finite vector is its total
coordinate mass. -/
theorem finiteBoundaryOneVector_inner
    {α : Type}
    [Fintype α]
    (p : FiniteBoundaryHilbert α) :
    inner ℝ (finiteBoundaryOneVector (α := α)) p =
      ∑ x : α, p x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro x _hx
  change p x * 1 = p x
  ring

/-- The anchored Perron matrix has trivial kernel whenever the normalized
transfer is symmetric and its fixed space is the line through one strictly
positive fixed vector. -/
theorem finiteKernelPerronAnchorMatrix_mulVec_eq_zero_imp
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    [Nonempty α]
    (kernel : α → α → ℝ)
    (hSymm :
      (finiteKernelNormalizedOperator kernel).toLinearMap.IsSymmetric)
    (p : FiniteBoundaryHilbert α)
    (hp : FiniteBoundaryPointwisePositive p)
    (hpfix : finiteKernelNormalizedOperator kernel p = p)
    (hline : ∀ g : FiniteBoundaryHilbert α,
      finiteKernelNormalizedOperator kernel g = g →
        ∃ c : ℝ, g = c • p)
    (v : α → ℝ)
    (hv : Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel) v = 0) :
    v = 0 := by
  classical
  let g : FiniteBoundaryHilbert α := WithLp.toLp 2 v
  let s : ℝ := ∑ x : α, v x
  have hpoint : ∀ output : α,
      g output - finiteKernelNormalizedOperator kernel g output + s = 0 := by
    intro output
    have hOutput := congrFun hv output
    rw [finiteKernelPerronAnchorMatrix_mulVec_apply] at hOutput
    simpa [g, s] using hOutput
  have hvec :
      g - finiteKernelNormalizedOperator kernel g +
          s • finiteBoundaryOneVector (α := α) = 0 := by
    ext output
    change
      g output - finiteKernelNormalizedOperator kernel g output + s * 1 = 0
    simpa using hpoint output
  have hcancel :
      inner ℝ (g - finiteKernelNormalizedOperator kernel g) p = 0 := by
    rw [inner_sub_left, hSymm g p, hpfix, sub_self]
  have hinner :
      inner ℝ
          (g - finiteKernelNormalizedOperator kernel g +
            s • finiteBoundaryOneVector (α := α)) p = 0 := by
    rw [hvec]
    simp
  have hsumPos : 0 < ∑ x : α, p x :=
    finiteBoundaryCoordinateSum_pos p hp
  have hsProd : s * (∑ x : α, p x) = 0 := by
    calc
      s * (∑ x : α, p x) =
          inner ℝ (s • finiteBoundaryOneVector (α := α)) p := by
        rw [real_inner_smul_left, finiteBoundaryOneVector_inner]
      _ = inner ℝ
          (g - finiteKernelNormalizedOperator kernel g +
            s • finiteBoundaryOneVector (α := α)) p := by
        rw [inner_add_left, hcancel, zero_add]
      _ = 0 := hinner
  have hs : s = 0 :=
    (mul_eq_zero.mp hsProd).resolve_right (ne_of_gt hsumPos)
  have hgfix : finiteKernelNormalizedOperator kernel g = g := by
    ext output
    have hOutput := hpoint output
    rw [hs] at hOutput
    simp only [add_zero] at hOutput
    linarith
  obtain ⟨c, hc⟩ := hline g hgfix
  have hsumScale := congrArg
    (fun z : FiniteBoundaryHilbert α => ∑ x : α, z x) hc
  have hsScale : s = c * (∑ x : α, p x) := by
    simpa [g, s, Finset.mul_sum] using hsumScale
  have hcZero : c = 0 := by
    rw [hs] at hsScale
    nlinarith
  have hgZero : g = 0 := by
    rw [hc, hcZero, zero_smul]
  funext output
  have hOutput := congrArg
    (fun z : FiniteBoundaryHilbert α => z output) hgZero
  simpa [g] using hOutput

/-- Under the same Perron fixed-line hypotheses, the anchored matrix has
nonzero determinant. -/
theorem finiteKernelPerronAnchorMatrix_det_ne_zero
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    [Nonempty α]
    (kernel : α → α → ℝ)
    (hSymm :
      (finiteKernelNormalizedOperator kernel).toLinearMap.IsSymmetric)
    (p : FiniteBoundaryHilbert α)
    (hp : FiniteBoundaryPointwisePositive p)
    (hpfix : finiteKernelNormalizedOperator kernel p = p)
    (hline : ∀ g : FiniteBoundaryHilbert α,
      finiteKernelNormalizedOperator kernel g = g →
        ∃ c : ℝ, g = c • p) :
    (finiteKernelPerronAnchorMatrix kernel).det ≠ 0 := by
  have hInjective :
      Function.Injective
        (Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel)) := by
    intro u v huv
    have hzero :
        Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel) (u - v) = 0 := by
      funext output
      change
        (∑ input : α,
          finiteKernelPerronAnchorMatrix kernel output input *
            (u input - v input)) = 0
      rw [Finset.sum_sub_distrib]
      change
        Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel) u output -
          Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel) v output = 0
      rw [congrFun huv output, sub_self]
    have huvZero :=
      finiteKernelPerronAnchorMatrix_mulVec_eq_zero_imp
        kernel hSymm p hp hpfix hline (u - v) hzero
    exact sub_eq_zero.mp huvZero
  have hUnit : IsUnit (finiteKernelPerronAnchorMatrix kernel) :=
    Matrix.mulVec_injective_iff_isUnit.mp hInjective
  exact
    ((Matrix.isUnit_iff_isUnit_det
      (finiteKernelPerronAnchorMatrix kernel)).mp hUnit).ne_zero

/-- Canonical Perron selector obtained by applying the inverse anchored matrix
to the constant-one vector. -/
noncomputable def finiteKernelCanonicalPerronGround
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    (kernel : α → α → ℝ) : FiniteBoundaryHilbert α :=
  WithLp.toLp 2
    (Matrix.mulVec
      (finiteRealNonsingularMatrixInverse
        (finiteKernelPerronAnchorMatrix kernel))
      (1 : α → ℝ))

/-- The canonical selector solves the anchored equation whenever the anchored
matrix is nonsingular. -/
theorem finiteKernelPerronAnchorMatrix_mulVec_canonical
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    (kernel : α → α → ℝ)
    (hdet : (finiteKernelPerronAnchorMatrix kernel).det ≠ 0) :
    Matrix.mulVec (finiteKernelPerronAnchorMatrix kernel)
        (fun x => finiteKernelCanonicalPerronGround kernel x) = 1 := by
  have hInverse :=
    mul_finiteRealNonsingularMatrixInverse
      (finiteKernelPerronAnchorMatrix kernel) hdet
  have hApply := congrArg
    (fun A : Matrix α α ℝ => Matrix.mulVec A (1 : α → ℝ)) hInverse
  rw [Matrix.mulVec_mulVec, Matrix.one_mulVec] at hApply
  simpa [finiteKernelCanonicalPerronGround] using hApply

/-- The canonical selector is the unique positive fixed vector whose coordinate
sum is one. -/
theorem finiteKernelCanonicalPerronGround_spec
    {α : Type}
    [Fintype α]
    [DecidableEq α]
    [Nonempty α]
    (kernel : α → α → ℝ)
    (hSymm :
      (finiteKernelNormalizedOperator kernel).toLinearMap.IsSymmetric)
    (p : FiniteBoundaryHilbert α)
    (hp : FiniteBoundaryPointwisePositive p)
    (hpfix : finiteKernelNormalizedOperator kernel p = p)
    (hline : ∀ g : FiniteBoundaryHilbert α,
      finiteKernelNormalizedOperator kernel g = g →
        ∃ c : ℝ, g = c • p) :
    (∑ x : α, finiteKernelCanonicalPerronGround kernel x = 1) ∧
    FiniteBoundaryPointwisePositive
      (finiteKernelCanonicalPerronGround kernel) ∧
    finiteKernelNormalizedOperator kernel
        (finiteKernelCanonicalPerronGround kernel) =
      finiteKernelCanonicalPerronGround kernel := by
  classical
  let g := finiteKernelCanonicalPerronGround kernel
  let s : ℝ := ∑ x : α, g x
  have hdet :=
    finiteKernelPerronAnchorMatrix_det_ne_zero
      kernel hSymm p hp hpfix hline
  have hanchor :=
    finiteKernelPerronAnchorMatrix_mulVec_canonical kernel hdet
  have hpoint : ∀ output : α,
      g output - finiteKernelNormalizedOperator kernel g output + s = 1 := by
    intro output
    have hOutput := congrFun hanchor output
    rw [finiteKernelPerronAnchorMatrix_mulVec_apply] at hOutput
    simpa [g, s] using hOutput
  have hvec :
      g - finiteKernelNormalizedOperator kernel g +
          s • finiteBoundaryOneVector (α := α) =
        finiteBoundaryOneVector (α := α) := by
    ext output
    change
      g output - finiteKernelNormalizedOperator kernel g output + s * 1 = 1
    simpa using hpoint output
  have hcancel :
      inner ℝ (g - finiteKernelNormalizedOperator kernel g) p = 0 := by
    rw [inner_sub_left, hSymm g p, hpfix, sub_self]
  have hsumPos : 0 < ∑ x : α, p x :=
    finiteBoundaryCoordinateSum_pos p hp
  have hsProd : s * (∑ x : α, p x) = ∑ x : α, p x := by
    calc
      s * (∑ x : α, p x) =
          inner ℝ (s • finiteBoundaryOneVector (α := α)) p := by
        rw [real_inner_smul_left, finiteBoundaryOneVector_inner]
      _ = inner ℝ
          (g - finiteKernelNormalizedOperator kernel g +
            s • finiteBoundaryOneVector (α := α)) p := by
        rw [inner_add_left, hcancel, zero_add]
      _ = inner ℝ (finiteBoundaryOneVector (α := α)) p := by
        rw [hvec]
      _ = ∑ x : α, p x := finiteBoundaryOneVector_inner p
  have hs : s = 1 := by
    apply (mul_left_cancel₀ (ne_of_gt hsumPos))
    simpa using hsProd
  have hgfix : finiteKernelNormalizedOperator kernel g = g := by
    ext output
    have hOutput := hpoint output
    rw [hs] at hOutput
    linarith
  obtain ⟨c, hc⟩ := hline g hgfix
  have hsumScale := congrArg
    (fun z : FiniteBoundaryHilbert α => ∑ x : α, z x) hc
  have hcScale : 1 = c * (∑ x : α, p x) := by
    simpa [s, hs, Finset.mul_sum] using hsumScale
  have hcPos : 0 < c := by
    nlinarith
  have hgPos : FiniteBoundaryPointwisePositive g := by
    intro output
    rw [hc]
    exact mul_pos hcPos (hp output)
  exact ⟨by simpa [g, s] using hs, by simpa [g] using hgPos,
    by simpa [g] using hgfix⟩

/-- The canonical Perron selector depends continuously on every continuous
finite kernel family satisfying the symmetric one-dimensional Perron fixed-line
hypotheses. -/
theorem continuous_finiteKernelCanonicalPerronGround
    {X α : Type}
    [TopologicalSpace X]
    [Fintype α]
    [DecidableEq α]
    [Nonempty α]
    (kernel : X → α → α → ℝ)
    (hkernel : ∀ input output : α,
      Continuous (fun x => kernel x input output))
    (hraw : ∀ x, finiteKernelOperator (kernel x) ≠ 0)
    (p : X → FiniteBoundaryHilbert α)
    (hSymm : ∀ x,
      (finiteKernelNormalizedOperator (kernel x)).toLinearMap.IsSymmetric)
    (hp : ∀ x, FiniteBoundaryPointwisePositive (p x))
    (hpfix : ∀ x,
      finiteKernelNormalizedOperator (kernel x) (p x) = p x)
    (hline : ∀ x (g : FiniteBoundaryHilbert α),
      finiteKernelNormalizedOperator (kernel x) g = g →
        ∃ c : ℝ, g = c • p x) :
    Continuous (fun x => finiteKernelCanonicalPerronGround (kernel x)) := by
  have hAnchor :=
    continuous_finiteKernelPerronAnchorMatrix kernel hkernel hraw
  have hdet : ∀ x,
      (finiteKernelPerronAnchorMatrix (kernel x)).det ≠ 0 := fun x =>
    finiteKernelPerronAnchorMatrix_det_ne_zero
      (kernel x) (hSymm x) (p x) (hp x) (hpfix x) (hline x)
  have hPlain : Continuous (fun x =>
      Matrix.mulVec
        (finiteRealNonsingularMatrixInverse
          (finiteKernelPerronAnchorMatrix (kernel x)))
        (1 : α → ℝ)) :=
    continuous_finiteRealNonsingularMatrixInverse_mulVec
      (fun x => finiteKernelPerronAnchorMatrix (kernel x))
      (fun _x => (1 : α → ℝ)) hAnchor continuous_const hdet
  simpa [finiteKernelCanonicalPerronGround] using
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.continuous.comp
      hPlain)

end

end MathlibAnalytic
end MGAP4D
