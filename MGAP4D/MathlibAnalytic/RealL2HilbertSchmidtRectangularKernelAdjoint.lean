import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtRectangularKernelOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {α : Type u} {β : Type u}
  [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Canonical synthesis operator attached to a rectangular real `L²` kernel.
It is the Hilbert adjoint of the Fréchet--Riesz analysis operator. -/
noncomputable def realL2HilbertSchmidtRectangularKernelSynthesisOperator
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 μ :=
  (realL2HilbertSchmidtRectangularKernelOperator
    (μ := μ) (ν := ν) K)†

/-- Exact matrix coefficient of the generic adjoint synthesis operator. -/
theorem realL2HilbertSchmidtRectangularKernelSynthesisOperator_inner
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (g : Lp ℝ 2 ν) (f : Lp ℝ 2 μ) :
    inner ℝ
        (realL2HilbertSchmidtRectangularKernelSynthesisOperator K g) f =
      realL2HilbertSchmidtKernelPairing K f g := by
  let A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 ν :=
    realL2HilbertSchmidtRectangularKernelOperator
      (μ := μ) (ν := ν) K
  calc
    inner ℝ
        (realL2HilbertSchmidtRectangularKernelSynthesisOperator K g) f =
      inner ℝ g (A f) := by
        exact ContinuousLinearMap.adjoint_inner_left A f g
    _ = inner ℝ (A f) g := by
      exact real_inner_comm _ _
    _ = realL2HilbertSchmidtKernelPairing K f g := by
      exact realL2HilbertSchmidtRectangularKernelOperator_inner K f g

/-- Analysis and synthesis have exactly the same operator norm. -/
theorem realL2HilbertSchmidtRectangularKernelSynthesisOperator_norm
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    ‖realL2HilbertSchmidtRectangularKernelSynthesisOperator K‖ =
      ‖realL2HilbertSchmidtRectangularKernelOperator K‖ := by
  simp [realL2HilbertSchmidtRectangularKernelSynthesisOperator]

/-- A vector with all synthesis matrix coefficients is the canonical adjoint
synthesis vector.  This is the quotient-level uniqueness principle used to
identify concrete integral sections without defining a second pointwise
operator representative. -/
theorem realL2HilbertSchmidtRectangularKernel_eq_synthesisOperator_of_inner_eq
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν))
    (g : Lp ℝ 2 ν)
    (v : Lp ℝ 2 μ)
    (hinner : ∀ f : Lp ℝ 2 μ,
      inner ℝ v f = realL2HilbertSchmidtKernelPairing K f g) :
    v = realL2HilbertSchmidtRectangularKernelSynthesisOperator K g := by
  let w := realL2HilbertSchmidtRectangularKernelSynthesisOperator K g
  have hcoeff : ∀ f : Lp ℝ 2 μ, inner ℝ v f = inner ℝ w f := by
    intro f
    exact (hinner f).trans
      (realL2HilbertSchmidtRectangularKernelSynthesisOperator_inner K g f).symm
  have hdiff := hcoeff (v - w)
  have hself : inner ℝ (v - w) (v - w) = 0 := by
    rw [inner_sub_left, hdiff]
    simp
  have hnormsq : ‖v - w‖ ^ 2 = 0 := by
    simpa using hself
  have hnorm : ‖v - w‖ = 0 := by
    nlinarith [norm_nonneg (v - w)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Audit-visible generic rectangular analysis/adjoint-synthesis package. -/
structure RealL2HilbertSchmidtRectangularKernelAdjointPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) : Prop where
  synthesisInner :
    ∀ (g : Lp ℝ 2 ν) (f : Lp ℝ 2 μ),
      inner ℝ
          (realL2HilbertSchmidtRectangularKernelSynthesisOperator K g) f =
        realL2HilbertSchmidtKernelPairing K f g
  synthesisNorm :
    ‖realL2HilbertSchmidtRectangularKernelSynthesisOperator K‖ =
      ‖realL2HilbertSchmidtRectangularKernelOperator K‖

/-- Construct the generic rectangular adjoint-synthesis receipt. -/
theorem realL2HilbertSchmidtRectangularKernelAdjointPackage
    [SFinite μ] [SFinite ν]
    (K : Lp ℝ 2 (μ.prod ν)) :
    RealL2HilbertSchmidtRectangularKernelAdjointPackage K :=
  { synthesisInner :=
      realL2HilbertSchmidtRectangularKernelSynthesisOperator_inner K
    synthesisNorm :=
      realL2HilbertSchmidtRectangularKernelSynthesisOperator_norm K }

end

end MathlibAnalytic
end MGAP4D
