import MGAP4D.MathlibAnalytic.FiniteRealInnerProbeGramNondegeneracy
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct InnerProductSpace

noncomputable section

/-- The raw coordinate map associated with a finite family of real
inner-product probes.  No norm or inner product is placed on the coordinate
space: the `i`-th coordinate is simply `⟪probe i, w⟫_ℝ`. -/
noncomputable def finiteRealInnerProbeRawLinearMap
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*}
    (probe : ι → W) :
    W →ₗ[ℝ] (ι → ℝ) where
  toFun := fun w i => inner ℝ (probe i) w
  map_add' := by
    intro x y
    funext i
    exact inner_add_right _ _ _
  map_smul' := by
    intro c x
    funext i
    exact real_inner_smul_right _ _ _

@[simp] theorem finiteRealInnerProbeRawLinearMap_apply
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*}
    (probe : ι → W) (w : W) (i : ι) :
    finiteRealInnerProbeRawLinearMap probe w i = inner ℝ (probe i) w :=
  rfl

/-- The square finite pairing matrix between probes `q_i` and vectors `v_j`:

`B i j = ⟪q_i, v_j⟫_ℝ`.

Unlike the probe-coordinate Gram matrix, this matrix contains only the pairings
that an explicit character, tensor-degree, or cylinder calculation must
evaluate. -/
noncomputable def finiteRealInnerProbePairingMatrix
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*}
    (probe v : ι → W) : Matrix ι ι ℝ :=
  fun i j => inner ℝ (probe i) (v j)

@[simp] theorem finiteRealInnerProbePairingMatrix_apply
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*}
    (probe v : ι → W) (i j : ι) :
    finiteRealInnerProbePairingMatrix probe v i j =
      inner ℝ (probe i) (v j) :=
  rfl

/-- An invertible finite pairing matrix separates the original Hilbert-space
family.

The proof is purely finite-dimensional on the probe side.  Nonzero determinant
gives linear independence of the matrix columns.  Those columns are exactly
the raw probe-coordinate images of `v_j`; linear independence after a linear
map implies linear independence before it. -/
theorem linearIndependent_of_finiteRealInnerProbePairingMatrix_det_ne_zero
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (probe v : ι → W)
    (hdet : (finiteRealInnerProbePairingMatrix probe v).det ≠ 0) :
    LinearIndependent ℝ v := by
  have hcols :
      LinearIndependent ℝ
        (fun j : ι => fun i : ι =>
          finiteRealInnerProbePairingMatrix probe v i j) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hcoords :
      LinearIndependent ℝ
        (fun j : ι => finiteRealInnerProbeRawLinearMap probe (v j)) := by
    simpa [finiteRealInnerProbePairingMatrix,
      finiteRealInnerProbeRawLinearMap] using hcols
  apply LinearIndependent.of_comp (finiteRealInnerProbeRawLinearMap probe)
  simpa [Function.comp_def] using hcoords

/-- Therefore a nonzero finite pairing determinant forces the ordinary Gram
determinant of the original Hilbert-space family to be nonzero. -/
theorem gram_det_ne_zero_of_finiteRealInnerProbePairingMatrix_det_ne_zero
    {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (probe v : ι → W)
    (hdet : (finiteRealInnerProbePairingMatrix probe v).det ≠ 0) :
    (Matrix.gram ℝ v).det ≠ 0 := by
  exact (Matrix.det_gram_ne_zero_iff_linearIndependent).mpr
    (linearIndependent_of_finiteRealInnerProbePairingMatrix_det_ne_zero
      probe v hdet)

end

end MathlibAnalytic
end MGAP4D
