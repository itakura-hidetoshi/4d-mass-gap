import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompressionQuadraticPackage

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProduct

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The orthogonal leakage of an ambient operator away from the analyzed
Hilbert subspace.  It compares the ambient action `T A` with the action
reconstructed from the canonical compression `A (A† T A)`. -/
noncomputable def realHilbertIsometricAdjointCompressionGeneratorDefect
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    F →L[ℝ] E :=
  (T ∘L A.toContinuousLinearMap) -
    (A.toContinuousLinearMap ∘L
      realHilbertIsometricAdjointCompression A T)

@[simp] theorem
    realHilbertIsometricAdjointCompressionGeneratorDefect_apply
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x : F) :
    realHilbertIsometricAdjointCompressionGeneratorDefect A T x =
      T (A x) - A (realHilbertIsometricAdjointCompression A T x) :=
  rfl

/-- The ambient action splits into its canonically reconstructed analyzed
component and the generator defect. -/
theorem realHilbertIsometricAdjointCompressionGeneratorDefect_decomposition
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x : F) :
    T (A x) =
      A (realHilbertIsometricAdjointCompression A T x) +
        realHilbertIsometricAdjointCompressionGeneratorDefect A T x := by
  rw [realHilbertIsometricAdjointCompressionGeneratorDefect_apply]
  abel

/-- The generator defect is orthogonal to every analyzed vector. -/
theorem realHilbertIsometricAdjointCompressionGeneratorDefect_inner_analysis
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x y : F) :
    inner ℝ
        (realHilbertIsometricAdjointCompressionGeneratorDefect A T x)
        (A y) = 0 := by
  rw [realHilbertIsometricAdjointCompressionGeneratorDefect_apply,
    inner_sub_left,
    ← realHilbertIsometricAdjointCompression_inner A T x y,
    A.inner_map_map]
  exact sub_self _

/-- Applying the adjoint synthesis to the defect gives zero. -/
theorem realHilbertAdjointSynthesis_generatorDefect
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x : F) :
    realHilbertAdjointSynthesis A
      (realHilbertIsometricAdjointCompressionGeneratorDefect A T x) = 0 := by
  rw [realHilbertIsometricAdjointCompressionGeneratorDefect_apply, map_sub,
    realHilbertIsometricAdjointCompression_apply,
    realHilbertAdjointSynthesis_analysis, sub_self]

/-- The ambient energy of an analyzed vector is the sum of the reconstructed
boundary energy and the orthogonal leakage energy. -/
theorem realHilbertIsometricAdjointCompressionGeneratorDefect_inner_self_decomposition
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x : F) :
    inner ℝ (T (A x)) (T (A x)) =
      inner ℝ
          (realHilbertIsometricAdjointCompression A T x)
          (realHilbertIsometricAdjointCompression A T x) +
        inner ℝ
          (realHilbertIsometricAdjointCompressionGeneratorDefect A T x)
          (realHilbertIsometricAdjointCompressionGeneratorDefect A T x) := by
  let K := realHilbertIsometricAdjointCompression A T
  let D := realHilbertIsometricAdjointCompressionGeneratorDefect A T
  have hdecomp : T (A x) = A (K x) + D x :=
    realHilbertIsometricAdjointCompressionGeneratorDefect_decomposition A T x
  have hDA : inner ℝ (D x) (A (K x)) = 0 :=
    realHilbertIsometricAdjointCompressionGeneratorDefect_inner_analysis
      A T x (K x)
  have hAD : inner ℝ (A (K x)) (D x) = 0 := by
    rw [real_inner_comm]
    exact hDA
  rw [hdecomp, inner_add_left, inner_add_right, inner_add_right,
    hAD, hDA, add_zero, zero_add, A.inner_map_map]

/-- Exact generator intertwining is equivalent to vanishing of the defect. -/
theorem realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0 ↔
      ∀ x : F,
        T (A x) = A (realHilbertIsometricAdjointCompression A T x) := by
  constructor
  · intro hD x
    have hx := congrArg
      (fun D : F →L[ℝ] E => D x) hD
    simpa [realHilbertIsometricAdjointCompressionGeneratorDefect_apply]
      using sub_eq_zero.mp hx
  · intro hintertwine
    apply ContinuousLinearMap.ext
    intro x
    rw [realHilbertIsometricAdjointCompressionGeneratorDefect_apply,
      hintertwine x, sub_self]

/-- Generator-level invariance of the analyzed range. -/
def realHilbertIsometricAdjointCompressionGeneratorRangeInvariant
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) : Prop :=
  ∀ x : F, ∃ y : F, T (A x) = A y

/-- Generator-level range invariance is exactly vanishing of the canonical
orthogonal defect. -/
theorem
    realHilbertIsometricAdjointCompressionGeneratorRangeInvariant_iff_defect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    realHilbertIsometricAdjointCompressionGeneratorRangeInvariant A T ↔
      realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0 := by
  constructor
  · intro hRange
    apply ContinuousLinearMap.ext
    intro x
    rcases hRange x with ⟨y, hy⟩
    have hK : realHilbertIsometricAdjointCompression A T x = y :=
      realHilbertIsometricAdjointCompression_apply_eq_of_analysis_eq
        A T x y hy
    rw [realHilbertIsometricAdjointCompressionGeneratorDefect_apply,
      hy, hK, sub_self]
  · intro hD x
    refine ⟨realHilbertIsometricAdjointCompression A T x, ?_⟩
    exact
      (realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff
        A T).mp hD x

/-- Vanishing of every defect energy is equivalent to vanishing of the defect
operator. -/
theorem
    realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff_inner_self
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0 ↔
      ∀ x : F,
        inner ℝ
          (realHilbertIsometricAdjointCompressionGeneratorDefect A T x)
          (realHilbertIsometricAdjointCompressionGeneratorDefect A T x) = 0 := by
  constructor
  · intro hD x
    rw [hD]
    simp
  · intro hEnergy
    apply ContinuousLinearMap.ext
    intro x
    have hnorm :
        ‖realHilbertIsometricAdjointCompressionGeneratorDefect A T x‖ ^ 2 = 0 := by
      simpa [real_inner_self_eq_norm_sq] using hEnergy x
    have hnorm0 :
        ‖realHilbertIsometricAdjointCompressionGeneratorDefect A T x‖ = 0 :=
      sq_eq_zero_iff.mp hnorm
    exact norm_eq_zero.mp hnorm0

/-- If the generator defect vanishes, every natural power intertwines through
the analysis isometry. -/
theorem realHilbertIsometricAdjointCompression_pow_analysis_apply_of_defect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (n : ℕ)
    (x : F) :
    (T ^ n) (A x) =
      A ((realHilbertIsometricAdjointCompression A T ^ n) x) := by
  let K := realHilbertIsometricAdjointCompression A T
  have hintertwine : ∀ y : F, T (A y) = A (K y) :=
    (realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff
      A T).mp hD
  induction n with
  | zero => simp [K]
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih, hintertwine,
        pow_succ', ContinuousLinearMap.mul_apply]

/-- Under zero generator defect, compressing every ambient natural power gives
exactly the corresponding power of the compressed generator. -/
theorem realHilbertIsometricAdjointCompression_pow_of_defect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hD : realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0)
    (n : ℕ) :
    realHilbertIsometricAdjointCompression A (T ^ n) =
      realHilbertIsometricAdjointCompression A T ^ n := by
  apply realHilbertIsometricAdjointCompression_eq_of_intertwines
  intro x
  exact realHilbertIsometricAdjointCompression_pow_analysis_apply_of_defect_eq_zero
    A T hD n x

/-- If a proposed boundary generator intertwines with the ambient generator,
then it is forced to be the canonical compression and the defect vanishes. -/
theorem realHilbertIsometricAdjointCompression_generator_unique
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (B : F →L[ℝ] F)
    (hintertwine : ∀ x : F, T (A x) = A (B x)) :
    B = realHilbertIsometricAdjointCompression A T ∧
      realHilbertIsometricAdjointCompressionGeneratorDefect A T = 0 := by
  have hB : realHilbertIsometricAdjointCompression A T = B :=
    realHilbertIsometricAdjointCompression_eq_of_intertwines
      A T B hintertwine
  constructor
  · exact hB.symm
  · rw [realHilbertIsometricAdjointCompressionGeneratorDefect_eq_zero_iff]
    intro x
    rw [hB]
    exact hintertwine x

end

end MathlibAnalytic
end MGAP4D