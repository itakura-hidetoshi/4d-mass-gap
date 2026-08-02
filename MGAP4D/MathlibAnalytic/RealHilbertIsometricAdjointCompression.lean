import MGAP4D.MathlibAnalytic.RealHilbertCenteredAdjointFactorization

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProductSpace

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Compress an ambient real-Hilbert-space operator through an isometric
analysis map and its canonical Hilbert adjoint synthesis. -/
noncomputable def realHilbertIsometricAdjointCompression
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    F →L[ℝ] F :=
  realHilbertAdjointSynthesis A ∘L
    (T ∘L A.toContinuousLinearMap)

@[simp] theorem realHilbertIsometricAdjointCompression_apply
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x : F) :
    realHilbertIsometricAdjointCompression A T x =
      realHilbertAdjointSynthesis A (T (A x)) :=
  rfl

/-- The adjoint synthesis of an isometric analysis is its exact left inverse. -/
theorem realHilbertAdjointSynthesis_analysis
    (A : F →ₗᵢ[ℝ] E)
    (x : F) :
    realHilbertAdjointSynthesis A (A x) = x := by
  apply ext_inner_right ℝ
  intro y
  unfold realHilbertAdjointSynthesis
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact A.inner_map_map x y

/-- Compression of the ambient identity is the boundary identity. -/
theorem realHilbertIsometricAdjointCompression_id
    (A : F →ₗᵢ[ℝ] E) :
    realHilbertIsometricAdjointCompression A
        (ContinuousLinearMap.id ℝ E) =
      ContinuousLinearMap.id ℝ F := by
  ext x
  change realHilbertAdjointSynthesis A (A x) = x
  exact realHilbertAdjointSynthesis_analysis A x

/-- The compressed matrix coefficient is the ambient matrix coefficient of
the analyzed vectors. -/
theorem realHilbertIsometricAdjointCompression_inner
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x y : F) :
    inner ℝ (realHilbertIsometricAdjointCompression A T x) y =
      inner ℝ (T (A x)) (A y) := by
  change
    inner ℝ (((A.toContinuousLinearMap)†) (T (A x))) y =
      inner ℝ (T (A x)) (A y)
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- If one analyzed vector is carried to another analyzed vector, adjoint
compression recovers the unique boundary vector exactly. -/
theorem realHilbertIsometricAdjointCompression_apply_eq_of_analysis_eq
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x y : F)
    (hxy : T (A x) = A y) :
    realHilbertIsometricAdjointCompression A T x = y := by
  rw [realHilbertIsometricAdjointCompression_apply, hxy]
  exact realHilbertAdjointSynthesis_analysis A y

/-- Exact ambient intertwining determines the compressed boundary operator. -/
theorem realHilbertIsometricAdjointCompression_eq_of_intertwines
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (B : F →L[ℝ] F)
    (hintertwine : ∀ x, T (A x) = A (B x)) :
    realHilbertIsometricAdjointCompression A T = B := by
  ext x
  exact realHilbertIsometricAdjointCompression_apply_eq_of_analysis_eq
    A T x (B x) (hintertwine x)

/-- Mere invariance of the analyzed range already makes the canonical
compression intertwine pointwise with the ambient operator. -/
theorem realHilbertIsometricAdjointCompression_analysis_apply_of_range
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hRange : ∀ x, ∃ y, T (A x) = A y)
    (x : F) :
    A (realHilbertIsometricAdjointCompression A T x) = T (A x) := by
  rcases hRange x with ⟨y, hy⟩
  have hcompression :
      realHilbertIsometricAdjointCompression A T x = y :=
    realHilbertIsometricAdjointCompression_apply_eq_of_analysis_eq
      A T x y hy
  rw [hcompression, hy]

end

end MathlibAnalytic
end MGAP4D
