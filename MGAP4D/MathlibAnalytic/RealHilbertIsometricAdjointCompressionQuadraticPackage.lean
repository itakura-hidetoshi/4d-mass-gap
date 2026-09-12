import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompression

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProduct

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The quadratic form of an isometric adjoint compression is exactly the
ambient quadratic form evaluated on the analyzed vector. -/
theorem realHilbertIsometricAdjointCompression_quadraticForm
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (x : F) :
    inner ℝ (realHilbertIsometricAdjointCompression A T x) x =
      inner ℝ (T (A x)) (A x) :=
  realHilbertIsometricAdjointCompression_inner A T x x

/-- Pairing symmetry of an ambient operator descends through isometric
adjoint compression. -/
theorem realHilbertIsometricAdjointCompression_inner_symm
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u v : E, inner ℝ (T u) v = inner ℝ u (T v))
    (x y : F) :
    inner ℝ (realHilbertIsometricAdjointCompression A T x) y =
      inner ℝ x (realHilbertIsometricAdjointCompression A T y) := by
  calc
    inner ℝ (realHilbertIsometricAdjointCompression A T x) y =
        inner ℝ (T (A x)) (A y) :=
      realHilbertIsometricAdjointCompression_inner A T x y
    _ = inner ℝ (A x) (T (A y)) := hT (A x) (A y)
    _ = inner ℝ (T (A y)) (A x) := real_inner_comm _ _
    _ = inner ℝ (realHilbertIsometricAdjointCompression A T y) x :=
      (realHilbertIsometricAdjointCompression_inner A T y x).symm
    _ = inner ℝ x (realHilbertIsometricAdjointCompression A T y) :=
      real_inner_comm _ _

/-- Nonnegativity of an ambient quadratic form descends through isometric
adjoint compression. -/
theorem realHilbertIsometricAdjointCompression_nonneg
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u : E, 0 ≤ inner ℝ (T u) u)
    (x : F) :
    0 ≤ inner ℝ (realHilbertIsometricAdjointCompression A T x) x := by
  rw [realHilbertIsometricAdjointCompression_quadraticForm]
  exact hT (A x)

/-- A global ambient coercivity estimate descends with the same constant
through an isometric analysis map. -/
theorem realHilbertIsometricAdjointCompression_coercive
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (gap : ℝ)
    (hT : ∀ u : E, gap * ‖u‖ ^ 2 ≤ inner ℝ (T u) u)
    (x : F) :
    gap * ‖x‖ ^ 2 ≤
      inner ℝ (realHilbertIsometricAdjointCompression A T x) x := by
  rw [realHilbertIsometricAdjointCompression_quadraticForm]
  simpa using hT (A x)

/-- It is enough to know coercivity only on the analyzed range. -/
theorem realHilbertIsometricAdjointCompression_coercive_on_range
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (gap : ℝ)
    (hT : ∀ x : F, gap * ‖A x‖ ^ 2 ≤ inner ℝ (T (A x)) (A x))
    (x : F) :
    gap * ‖x‖ ^ 2 ≤
      inner ℝ (realHilbertIsometricAdjointCompression A T x) x := by
  rw [realHilbertIsometricAdjointCompression_quadraticForm]
  simpa using hT x

/-- A strictly positive compressed coercivity constant excludes a nonzero
kernel vector. -/
theorem realHilbertIsometricAdjointCompression_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (gap : ℝ)
    (hgap : 0 < gap)
    (hT : ∀ u : E, gap * ‖u‖ ^ 2 ≤ inner ℝ (T u) u)
    (x : F)
    (hx : realHilbertIsometricAdjointCompression A T x = 0) :
    x = 0 := by
  have hcoercive :=
    realHilbertIsometricAdjointCompression_coercive A T gap hT x
  rw [hx, inner_zero_left] at hcoercive
  have hnormsq : ‖x‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)

/-- If the ambient operator annihilates the analyzed vacuum, then its
canonical compression annihilates the boundary vacuum. -/
theorem realHilbertIsometricAdjointCompression_vacuum
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (vacuum : F)
    (hvacuum : T (A vacuum) = 0) :
    realHilbertIsometricAdjointCompression A T vacuum = 0 := by
  exact realHilbertIsometricAdjointCompression_apply_eq_of_analysis_eq
    A T vacuum 0 (by simpa using hvacuum)

/-- A symmetric compressed operator that annihilates a vacuum has range
orthogonal to that vacuum. -/
theorem realHilbertIsometricAdjointCompression_range_orthogonal_to_vacuum
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (hT : ∀ u v : E, inner ℝ (T u) v = inner ℝ u (T v))
    (vacuum : F)
    (hvacuum : T (A vacuum) = 0)
    (x : F) :
    inner ℝ vacuum
      (realHilbertIsometricAdjointCompression A T x) = 0 := by
  have hcompressedVacuum :
      realHilbertIsometricAdjointCompression A T vacuum = 0 :=
    realHilbertIsometricAdjointCompression_vacuum A T vacuum hvacuum
  calc
    inner ℝ vacuum (realHilbertIsometricAdjointCompression A T x) =
        inner ℝ (realHilbertIsometricAdjointCompression A T x) vacuum :=
      real_inner_comm _ _
    _ = inner ℝ x
        (realHilbertIsometricAdjointCompression A T vacuum) :=
      realHilbertIsometricAdjointCompression_inner_symm A T hT x vacuum
    _ = 0 := by rw [hcompressedVacuum]; simp

end

end MathlibAnalytic
end MGAP4D
