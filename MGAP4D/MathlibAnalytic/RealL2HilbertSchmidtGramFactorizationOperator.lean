import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtGramPositiveKernel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

universe u v

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- Over a real Hilbert space, a symmetric Hilbert--Schmidt kernel pairing is
completely determined by its diagonal quadratic form.  Thus equality of
quadratic forms with `f ↦ ‖A f‖²` recovers the full Gram factorization by real
polarization. -/
theorem realL2HilbertSchmidtKernelPairing_gramFactorization_of_symmetric_of_quadratic
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hSymm : RealL2HilbertSchmidtKernelPairingSymmetric K)
    (hQuadratic : ∀ f : Lp ℝ 2 μ,
      realL2HilbertSchmidtKernelPairing K f f = inner ℝ (A f) (A f)) :
    RealL2HilbertSchmidtKernelPairingGramFactorization K H A := by
  intro f g
  have hsum := hQuadratic (f + g)
  have hff := hQuadratic f
  have hgg := hQuadratic g
  rw [realL2HilbertSchmidtKernelPairing_add_left,
    realL2HilbertSchmidtKernelPairing_add_right,
    realL2HilbertSchmidtKernelPairing_add_right] at hsum
  simp only [map_add] at hsum
  rw [inner_add_left, inner_add_right, inner_add_right] at hsum
  have hBsymm := hSymm g f
  have hIsymm : inner ℝ (A g) (A f) = inner ℝ (A f) (A g) :=
    real_inner_comm _ _
  nlinarith

/-- A quotient-level exact Gram factorization identifies the canonical square
Hilbert--Schmidt kernel operator with `A† A`.

This theorem is purely Hilbert-geometric: once all matrix coefficients of the
kernel pairing are those of the feature analysis map, no pointwise
representative of either boundary-operator output is needed. -/
theorem realL2HilbertSchmidtKernelOperator_eq_adjoint_comp_of_gramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) :
    realL2HilbertSchmidtKernelOperator K = (A†).comp A := by
  apply ContinuousLinearMap.ext
  intro f
  let T := realL2HilbertSchmidtKernelOperator K
  let P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ := (A†).comp A
  have hinner : ∀ g : Lp ℝ 2 μ,
      inner ℝ (T f) g = inner ℝ (P f) g := by
    intro g
    rw [show inner ℝ (T f) g =
        realL2HilbertSchmidtKernelPairing K f g by
      exact realL2HilbertSchmidtKernelOperator_inner K f g]
    rw [hGram f g]
    change inner ℝ (A f) (A g) = inner ℝ ((A†) (A f)) g
    rw [ContinuousLinearMap.adjoint_inner_left]
  have hdiff := hinner (T f - P f)
  have hself : inner ℝ (T f - P f) (T f - P f) = 0 := by
    rw [inner_sub_left, hdiff]
    simp
  have hnormsq : ‖T f - P f‖ ^ 2 = 0 := by
    simpa using hself
  have hnorm : ‖T f - P f‖ = 0 := by
    nlinarith [norm_nonneg (T f - P f)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- The same exact factorization immediately transfers the square-kernel
operator norm to the `C*` identity `‖T_K‖ = ‖A‖²`. -/
theorem realL2HilbertSchmidtKernelOperator_norm_eq_analysis_sq_of_gramFactorization
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) :
    ‖realL2HilbertSchmidtKernelOperator K‖ = ‖A‖ ^ 2 := by
  rw [realL2HilbertSchmidtKernelOperator_eq_adjoint_comp_of_gramFactorization
    K H A hGram]
  rw [ContinuousLinearMap.norm_adjoint_comp_self]
  ring

/-- Audit-visible exact operator-factorization receipt. -/
structure RealL2HilbertSchmidtGramFactorizationOperatorPackage
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) : Prop where
  operatorEq :
    realL2HilbertSchmidtKernelOperator K = (A†).comp A
  operatorNormEq :
    ‖realL2HilbertSchmidtKernelOperator K‖ = ‖A‖ ^ 2

/-- Construct the generic exact operator-factorization receipt. -/
theorem realL2HilbertSchmidtGramFactorizationOperatorPackage
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (H : Type v)
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : Lp ℝ 2 μ →L[ℝ] H)
    (hGram : RealL2HilbertSchmidtKernelPairingGramFactorization K H A) :
    RealL2HilbertSchmidtGramFactorizationOperatorPackage K H A hGram :=
  { operatorEq :=
      realL2HilbertSchmidtKernelOperator_eq_adjoint_comp_of_gramFactorization
        K H A hGram
    operatorNormEq :=
      realL2HilbertSchmidtKernelOperator_norm_eq_analysis_sq_of_gramFactorization
        K H A hGram }

end

end MathlibAnalytic
end MGAP4D
