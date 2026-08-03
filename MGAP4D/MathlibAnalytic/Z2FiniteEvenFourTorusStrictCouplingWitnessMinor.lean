import MGAP4D.MathlibAnalytic.FiniteTensorProductKernelPosDef
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronGroundSpectrum
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct Matrix

noncomputable section

/-- Strict coupling separates the two local `Z₂` Wilson weights. -/
theorem z2WilsonWeightNontrivial_lt_identity
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    z2WilsonWeightNontrivial β energyNontrivial <
      z2WilsonWeightIdentity β energyIdentity := by
  unfold z2WilsonWeightNontrivial z2WilsonWeightIdentity
  apply Real.exp_lt_exp.mpr
  nlinarith

/-- The explicit local two-state kernel matrix. -/
noncomputable def z2PlaquetteKernelMatrix
    (w₀ w₁ : ℝ) : Matrix Bool Bool ℝ :=
  Matrix.of fun x y => z2PlaquetteKernel w₀ w₁ x y

/-- A two-state kernel with `0 < w₁ < w₀` is positive definite. -/
theorem z2PlaquetteKernelMatrix_posDef
    (w₀ w₁ : ℝ)
    (hw₁ : 0 < w₁)
    (hstrict : w₁ < w₀) :
    (z2PlaquetteKernelMatrix w₀ w₁).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · ext x y
    cases x <;> cases y <;>
      simp [z2PlaquetteKernelMatrix, z2PlaquetteKernel,
        Matrix.conjTranspose_apply]
  · intro x hx
    have hcoord : x false ≠ 0 ∨ x true ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext b
      cases b <;> simp [h]
    simp [z2PlaquetteKernelMatrix, z2PlaquetteKernel,
      dotProduct, Matrix.mulVec]
    rcases hcoord with hfalse | htrue
    · nlinarith [mul_self_pos.mpr hfalse,
        sq_nonneg (x false + x true)]
    · nlinarith [mul_self_pos.mpr htrue,
        sq_nonneg (x false + x true)]

/-- Strict physical coupling makes the actual local `Z₂` Wilson matrix
positive definite. -/
theorem z2GaugeWilsonPlaquetteKernelMatrix_posDef
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    (Matrix.of fun x y : Z2Gauge =>
      (z2GaugeWilsonPlaquetteGramKernel
        β energyIdentity energyNontrivial hβ.le hEnergy.le).kernel x y).PosDef := by
  let w₀ := z2WilsonWeightIdentity β energyIdentity
  let w₁ := z2WilsonWeightNontrivial β energyNontrivial
  have hbool : (z2PlaquetteKernelMatrix w₀ w₁).PosDef :=
    z2PlaquetteKernelMatrix_posDef w₀ w₁
      (z2WilsonWeightNontrivial_pos β energyNontrivial)
      (z2WilsonWeightNontrivial_lt_identity
        β energyIdentity energyNontrivial hβ hEnergy)
  have hsub := hbool.submatrix boolEquivZ2Gauge.symm.injective
  simpa [z2PlaquetteKernelMatrix,
    z2GaugeWilsonPlaquetteGramKernel,
    FiniteOSGramKernelOn.transport] using hsub

/-- Matrix of the temporal crossing kernel on the complete finite spatial-link
configuration space. -/
noncomputable def finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Matrix
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) ℝ :=
  Matrix.of fun A B =>
    (finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel A B

/-- The temporal crossing matrix is exactly the finite tensor product of the
local actual `Z₂` matrix over all spatial links. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix_eq_product
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix
        H β energyIdentity energyNontrivial hβ hEnergy =
      finiteProductKernelMatrix
        (FiniteEvenFourTorusSpatialLink H) Z2Gauge
        (Matrix.of fun x y : Z2Gauge =>
          (z2GaugeWilsonPlaquetteGramKernel
            β energyIdentity energyNontrivial hβ hEnergy).kernel x y) := by
  ext A B
  rw [finiteProductKernelMatrix_apply]
  unfold finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix
    finiteEvenFourTorusZ2TemporalGaugeCrossingGramKernel
  rw [finite_os_gram_kernel_listProduct_apply]
  simp [finiteEvenFourTorusZ2TemporalLinkGramKernel,
    FiniteOSGramKernelOn.comap]

/-- Under strict coupling the complete temporal crossing matrix is positive
definite at every finite side parameter. -/
theorem finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix_posDef
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    (finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).PosDef := by
  rw [finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix_eq_product]
  exact finiteProductKernelMatrix_posDef
    (FiniteEvenFourTorusSpatialLink H) Z2Gauge _
    (z2GaugeWilsonPlaquetteKernelMatrix_posDef
      β energyIdentity energyNontrivial hβ hEnergy)

/-- Matrix of the complete temporal-gauge one-slab kernel. -/
noncomputable def finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Matrix
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) ℝ :=
  Matrix.of fun A B =>
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel A B

/-- The full one-slab matrix is the positive diagonal congruence of the
crossing tensor matrix by the spatial half-weight. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix_eq_diagonal_congruence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix
        H β energyIdentity energyNontrivial hβ hEnergy =
      Matrix.diagonal
          (finiteEvenFourTorusZ2SpatialHalfWeight
            H β energyIdentity energyNontrivial) *
        finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix
          H β energyIdentity energyNontrivial hβ hEnergy *
      Matrix.diagonal
        (finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial) := by
  classical
  ext A B
  simp [finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix,
    finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix,
    finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel,
    Matrix.mul_apply]

/-- Strict coupling makes the full temporal-gauge one-slab kernel matrix
positive definite at every finite side parameter. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix_posDef
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix
      H β energyIdentity energyNontrivial hβ.le hEnergy.le).PosDef := by
  classical
  let D : Matrix
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) ℝ :=
    Matrix.diagonal
      (finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial)
  have hD : D.PosDef :=
    Matrix.PosDef.diagonal fun A =>
      finiteEvenFourTorusZ2SpatialHalfWeight_pos
        H β energyIdentity energyNontrivial A
  have hC :=
    finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix_posDef
      H β energyIdentity energyNontrivial hβ hEnergy
  have hcongr :
      (Dᴴ *
        finiteEvenFourTorusZ2TemporalGaugeCrossingKernelMatrix
          H β energyIdentity energyNontrivial hβ.le hEnergy.le * D).PosDef :=
    hC.conjTranspose_mul_mul_same
      (Matrix.isLeftRegular_iff_mulVec_injective.mp hD.isUnit.isLeftRegular)
  have hDstar : Dᴴ = D := hD.isHermitian.eq
  rw [hDstar] at hcongr
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix_eq_diagonal_congruence]
  exact hcongr

/-- Positive definiteness of the column-oriented kernel matrix implies
injectivity of the associated finite Euclidean kernel operator. -/
theorem finiteKernelOperator_injective_of_columnMatrix_posDef
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ)
    (hpos : (Matrix.of fun y x => kernel x y).PosDef) :
    Function.Injective (finiteKernelOperator kernel) := by
  intro f g hfg
  apply sub_eq_zero.mp
  by_contra hne
  let z : FiniteBoundaryHilbert α := f - g
  have hzfun : (fun x : α => z x) ≠ 0 := by
    intro hz
    apply hne
    ext x
    exact congrFun hz x
  have hzop : finiteKernelOperator kernel z = 0 := by
    dsimp [z]
    rw [map_sub, hfg, sub_self]
  have hmul :
      (Matrix.of fun y x => kernel x y).mulVec (fun x => z x) = 0 := by
    funext y
    have hy := congrArg
      (fun w : FiniteBoundaryHilbert α => w y) hzop
    simpa [finiteKernelOperator_apply, Matrix.mulVec] using hy
  have hquad := hpos.dotProduct_mulVec_pos hzfun
  rw [hmul] at hquad
  simp at hquad

/-- The raw temporal-gauge one-slab transfer is injective under strict coupling
at every finite side parameter. -/
theorem finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_injective_strict
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Function.Injective
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  unfold finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer
  apply finiteKernelOperator_injective_of_columnMatrix_posDef
  have hpos :=
    finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix_posDef
      H β energyIdentity energyNontrivial hβ hEnergy
  simpa [finiteEvenFourTorusZ2TemporalGaugeOneSlabKernelMatrix,
    Matrix.transpose_apply] using hpos.transpose

/-- The normalized actual unfixed transfer is injective after compression to
the residual-Gauss-invariant Hilbert space in the strict-coupling regime. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_injective_strict
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Function.Injective
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  intro f g hfg
  apply Subtype.ext
  apply finiteEvenFourTorusZ2TemporalGaugeOneSlabRawTransfer_injective_strict
    H β energyIdentity energyNontrivial hβ hEnergy
  have hambient := congrArg
    (fun x : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H => x.1) hfg
  change
    ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
      H β energyIdentity energyNontrivial hβ.le hEnergy.le‖⁻¹ •
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le f.1 =
      ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le‖⁻¹ •
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le g.1 at hambient
  have hc :
      ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H β energyIdentity energyNontrivial hβ.le hEnergy.le‖⁻¹ ≠ 0 :=
    inv_ne_zero
      (norm_ne_zero_iff.mpr
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
          H β energyIdentity energyNontrivial hβ.le hEnergy.le))
  have hraw := smul_left_cancel₀ hc hambient
  rw [finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_apply_invariant
      H β energyIdentity energyNontrivial hβ.le hEnergy.le f,
    finiteEvenFourTorusZ2UnfixedGaugeRawTransfer_apply_invariant
      H β energyIdentity energyNontrivial hβ.le hEnergy.le g] at hraw
  exact hraw

namespace FiniteDimensionalSymmetricPositiveContractionData

variable
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (D : FiniteDimensionalSymmetricPositiveContractionData E)

/-- Injectivity of a finite symmetric positive contraction excludes every null
spectral index. -/
theorem not_nonempty_nullSpectralIndex_of_operator_injective
    (hinj : Function.Injective D.operator) :
    ¬ Nonempty D.NullSpectralIndex := by
  rintro ⟨i⟩
  have hzero : D.operator (D.eigenbasis i.1) = 0 := by
    rw [D.operator_apply_eigenbasis i.1, i.2, zero_smul]
  have heq : D.eigenbasis i.1 = 0 := by
    apply hinj
    simpa using hzero
  exact D.eigenbasis_orthonormal.ne_zero i.1 heq

end FiniteDimensionalSymmetricPositiveContractionData

/-- Strict coupling removes the null spectral sector of the actual compressed
unfixed-gauge transfer at every finite side parameter. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    ¬ Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) :=
  (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      .not_nonempty_nullSpectralIndex_of_operator_injective
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_injective_strict
          H β energyIdentity energyNontrivial hβ hEnergy)

/-- Combining side-two nonidentity with strict-coupling null-sector absence
makes the strictly excited spectral sector unconditionally inhabited. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex_nonempty_strict
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) :
    Nonempty
      (FiniteEvenFourTorusZ2UnfixedGaugeExcitedSpectralIndex
        0 β energyIdentity energyNontrivial hβ.le hEnergy.le) := by
  rcases finiteEvenFourTorusZ2UnfixedGaugeExcitedOrNullSpectralIndex_nonempty
      β energyIdentity energyNontrivial hβ.le hEnergy.le with hexc | hnull
  · exact hexc
  · exact False.elim
      (finiteEvenFourTorusZ2UnfixedGaugeNullSpectralIndex_not_nonempty_strict
        0 β energyIdentity energyNontrivial hβ hEnergy hnull)

end

end MathlibAnalytic
end MGAP4D
