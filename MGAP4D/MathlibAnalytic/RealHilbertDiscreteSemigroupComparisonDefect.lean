import MGAP4D.MathlibAnalytic.RealHilbertIsometricAdjointCompressionGeneratorDefect
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped InnerProduct

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The exact discrepancy between two bounded discrete semigroups at natural
 time `n`.  No relation between the two one-step operators is assumed. -/
noncomputable def realHilbertDiscreteSemigroupComparisonDefect
    (T S : E →L[ℝ] E)
    (n : ℕ) :
    E →L[ℝ] E :=
  T ^ n - S ^ n

@[simp] theorem realHilbertDiscreteSemigroupComparisonDefect_zero
    (T S : E →L[ℝ] E) :
    realHilbertDiscreteSemigroupComparisonDefect T S 0 = 0 := by
  simp [realHilbertDiscreteSemigroupComparisonDefect]

@[simp] theorem realHilbertDiscreteSemigroupComparisonDefect_one
    (T S : E →L[ℝ] E) :
    realHilbertDiscreteSemigroupComparisonDefect T S 1 = T - S := by
  simp [realHilbertDiscreteSemigroupComparisonDefect]

/-- Exact noncommutative successor decomposition.  It separates the propagated
old discrepancy from the newly inserted one-step discrepancy. -/
theorem realHilbertDiscreteSemigroupComparisonDefect_succ
    (T S : E →L[ℝ] E)
    (n : ℕ) :
    realHilbertDiscreteSemigroupComparisonDefect T S (n + 1) =
      T ^ n * (T - S) +
        realHilbertDiscreteSemigroupComparisonDefect T S n * S := by
  unfold realHilbertDiscreteSemigroupComparisonDefect
  rw [pow_succ, pow_succ]
  noncomm_ring

/-- Equality of the one-step operators forces exact equality at every natural
 time. -/
theorem realHilbertDiscreteSemigroupComparisonDefect_eq_zero_of_step_eq
    (T S : E →L[ℝ] E)
    (hTS : T = S)
    (n : ℕ) :
    realHilbertDiscreteSemigroupComparisonDefect T S n = 0 := by
  subst S
  simp [realHilbertDiscreteSemigroupComparisonDefect]

/-- Vanishing of the comparison defect at time one already identifies the two
one-step operators. -/
theorem realHilbertDiscreteSemigroupComparisonDefect_one_eq_zero_iff
    (T S : E →L[ℝ] E) :
    realHilbertDiscreteSemigroupComparisonDefect T S 1 = 0 ↔ T = S := by
  rw [realHilbertDiscreteSemigroupComparisonDefect_one, sub_eq_zero]

/-- Exact equality of the complete natural-time families is equivalent to
one-step equality. -/
theorem realHilbertDiscreteSemigroupComparisonDefect_all_eq_zero_iff
    (T S : E →L[ℝ] E) :
    (∀ n : ℕ,
      realHilbertDiscreteSemigroupComparisonDefect T S n = 0) ↔
      T = S := by
  constructor
  · intro h
    exact
      (realHilbertDiscreteSemigroupComparisonDefect_one_eq_zero_iff T S).mp
        (h 1)
  · intro h n
    exact realHilbertDiscreteSemigroupComparisonDefect_eq_zero_of_step_eq
      T S h n

/-- A genuine one-step discrepancy is an exact no-go witness for equality of
the complete discrete semigroups. -/
theorem realHilbertDiscreteSemigroupComparisonDefect_exists_ne_zero_of_step_ne
    (T S : E →L[ℝ] E)
    (hTS : T ≠ S) :
    ∃ n : ℕ,
      realHilbertDiscreteSemigroupComparisonDefect T S n ≠ 0 := by
  refine ⟨1, ?_⟩
  intro h
  exact hTS
    ((realHilbertDiscreteSemigroupComparisonDefect_one_eq_zero_iff T S).mp h)

/-- Comparison of an ambient discrete step with a prescribed boundary step
through a real linear isometry.  This defect is deliberately distinct from the
canonical compression defect: the boundary operator is supplied independently
and need not equal the adjoint compression. -/
noncomputable def realHilbertIsometricDiscreteStepComparisonDefect
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F) :
    F →L[ℝ] E :=
  (T ∘L A.toContinuousLinearMap) -
    (A.toContinuousLinearMap ∘L S)

@[simp] theorem realHilbertIsometricDiscreteStepComparisonDefect_apply
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F)
    (x : F) :
    realHilbertIsometricDiscreteStepComparisonDefect A T S x =
      T (A x) - A (S x) :=
  rfl

/-- The supplied-step comparison defect vanishes exactly when the one-step
intertwining identity holds pointwise. -/
theorem realHilbertIsometricDiscreteStepComparisonDefect_eq_zero_iff
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F) :
    realHilbertIsometricDiscreteStepComparisonDefect A T S = 0 ↔
      ∀ x : F, T (A x) = A (S x) := by
  constructor
  · intro h x
    have hx := congrArg
      (fun D : F →L[ℝ] E => D x) h
    simpa [realHilbertIsometricDiscreteStepComparisonDefect_apply]
      using sub_eq_zero.mp hx
  · intro h
    apply ContinuousLinearMap.ext
    intro x
    rw [realHilbertIsometricDiscreteStepComparisonDefect_apply,
      h x, sub_self]
    rfl

/-- When the independently supplied boundary step is the canonical adjoint
compression, the discrete comparison defect is exactly the existing canonical
orthogonal generator defect. -/
theorem realHilbertIsometricDiscreteStepComparisonDefect_eq_generatorDefect
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E) :
    realHilbertIsometricDiscreteStepComparisonDefect A T
        (realHilbertIsometricAdjointCompression A T) =
      realHilbertIsometricAdjointCompressionGeneratorDefect A T :=
  rfl

/-- One-step intertwining propagates to every natural power. -/
theorem realHilbertIsometricDiscreteStepComparison_pow_apply_of_defect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F)
    (hD : realHilbertIsometricDiscreteStepComparisonDefect A T S = 0)
    (n : ℕ)
    (x : F) :
    (T ^ n) (A x) = A ((S ^ n) x) := by
  have hOne : ∀ y : F, T (A y) = A (S y) :=
    (realHilbertIsometricDiscreteStepComparisonDefect_eq_zero_iff
      A T S).mp hD
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ, pow_succ,
        ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
      rw [hOne x, ih (S x)]

/-- Exact one-step intertwining gives exact adjoint compression of every natural
power, even when the supplied boundary step was not defined by compression. -/
theorem realHilbertIsometricAdjointCompression_pow_eq_of_discreteStepComparisonDefect_eq_zero
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F)
    (hD : realHilbertIsometricDiscreteStepComparisonDefect A T S = 0)
    (n : ℕ) :
    realHilbertIsometricAdjointCompression A (T ^ n) = S ^ n := by
  apply ContinuousLinearMap.ext
  intro x
  rw [realHilbertIsometricAdjointCompression_apply,
    realHilbertIsometricDiscreteStepComparison_pow_apply_of_defect_eq_zero
      A T S hD n x,
    realHilbertAdjointSynthesis_analysis]

/-- Conversely, equality of the compressed natural-time family at time one
identifies the supplied boundary step with the canonical compression. -/
theorem realHilbertIsometricAdjointCompression_eq_of_pow_family_eq
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F)
    (hFamily : ∀ n : ℕ,
      realHilbertIsometricAdjointCompression A (T ^ n) = S ^ n) :
    realHilbertIsometricAdjointCompression A T = S := by
  simpa using hFamily 1

/-- A nonzero supplied-step comparison defect is an exact obstruction to any
all-natural-time ambient/boundary intertwining theorem. -/
theorem realHilbertIsometricDiscreteStepComparison_no_go
    (A : F →ₗᵢ[ℝ] E)
    (T : E →L[ℝ] E)
    (S : F →L[ℝ] F)
    (hD : realHilbertIsometricDiscreteStepComparisonDefect A T S ≠ 0) :
    ¬ (∀ n : ℕ, ∀ x : F,
      (T ^ n) (A x) = A ((S ^ n) x)) := by
  intro hAll
  apply hD
  apply
    (realHilbertIsometricDiscreteStepComparisonDefect_eq_zero_iff
      A T S).2
  intro x
  simpa using hAll 1 x

end

end MathlibAnalytic
end MGAP4D
