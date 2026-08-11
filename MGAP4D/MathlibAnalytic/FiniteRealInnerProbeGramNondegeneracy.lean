import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.LinearIndependent.Basic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

/-- A finite family of real inner-product probes, bundled as a linear map into
finite Euclidean coordinates.  The `i`-th coordinate of `probeMap w` is
`⟪probe i, w⟫_ℝ`. -/
noncomputable def finiteRealInnerProbeLinearMap
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι]
    (probe : ι → W) :
    W →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun := fun w =>
    WithLp.toLp 2 fun i => inner ℝ (probe i) w
  map_add' := by
    intro x y
    ext i
    change inner ℝ (probe i) (x + y) =
      inner ℝ (probe i) x + inner ℝ (probe i) y
    exact inner_add_right _ _ _
  map_smul' := by
    intro c x
    ext i
    change inner ℝ (probe i) (c • x) = c * inner ℝ (probe i) x
    exact real_inner_smul_right _ _ _

@[simp] theorem finiteRealInnerProbeLinearMap_apply
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι]
    (probe : ι → W) (w : W) (i : ι) :
    finiteRealInnerProbeLinearMap probe w i = inner ℝ (probe i) w :=
  rfl

/-- Gram matrix of the finite Euclidean coordinate vectors obtained by probing
a family `v` against another family `probe` with the real inner product. -/
noncomputable def finiteRealInnerProbeGramMatrix
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι]
    (probe v : ι → W) : Matrix ι ι ℝ :=
  Matrix.gram ℝ (fun j => finiteRealInnerProbeLinearMap probe (v j))

/-- If the finite probe-coordinate Gram determinant is nonzero, then the
original family is linearly independent.

This direction needs no injectivity assumption on the probe map: linear
independence after applying a linear map already implies linear independence
before applying it. -/
theorem linearIndependent_of_finiteRealInnerProbeGramMatrix_det_ne_zero
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (probe v : ι → W)
    (hdet : (finiteRealInnerProbeGramMatrix probe v).det ≠ 0) :
    LinearIndependent ℝ v := by
  have hprobe :
      LinearIndependent ℝ
        (fun j => finiteRealInnerProbeLinearMap probe (v j)) :=
    Matrix.linearIndependent_of_det_gram_ne_zero hdet
  apply LinearIndependent.of_comp (finiteRealInnerProbeLinearMap probe)
  simpa [Function.comp_def] using hprobe

/-- A nonzero finite probe-coordinate Gram determinant therefore forces the
ordinary Gram determinant of the original family to be nonzero. -/
theorem gram_det_ne_zero_of_finiteRealInnerProbeGramMatrix_det_ne_zero
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (probe v : ι → W)
    (hdet : (finiteRealInnerProbeGramMatrix probe v).det ≠ 0) :
    (Matrix.gram ℝ v).det ≠ 0 := by
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent).mpr
    (linearIndependent_of_finiteRealInnerProbeGramMatrix_det_ne_zero
      probe v hdet)

end

end MathlibAnalytic
end MGAP4D
