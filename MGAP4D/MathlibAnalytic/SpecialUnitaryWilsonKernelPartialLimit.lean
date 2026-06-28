import MGAP4D.MathlibAnalytic.SpecialUnitaryNormalizedTraceKernelFeature
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace MGAP4D
namespace MathlibAnalytic

open Filter NormedSpace
open scoped BigOperators Topology

noncomputable section

/-- The recursively defined finite exponential kernel is the ordinary partial
sum of the scalar exponential series. -/
theorem RealHilbertKernelFeature.exponentialPartialKernel_eq_sum
    {X : Type}
    (kernel : X → X → ℝ)
    (c : ℝ)
    (n : ℕ)
    (x y : X) :
    RealHilbertKernelFeature.exponentialPartialKernel kernel c n x y =
      ∑ m ∈ Finset.range (n + 1),
        (c * kernel x y) ^ m / (Nat.factorial m : ℝ) := by
  induction n with
  | zero =>
      simp [RealHilbertKernelFeature.exponentialPartialKernel]
  | succ n ih =>
      change
        RealHilbertKernelFeature.exponentialPartialKernel kernel c n x y +
            (c ^ (n + 1) / (Nat.factorial (n + 1) : ℝ)) *
              kernel x y ^ (n + 1) =
          ∑ m ∈ Finset.range (n + 1 + 1),
            (c * kernel x y) ^ m / (Nat.factorial m : ℝ)
      rw [ih]
      conv_rhs => rw [Finset.sum_range_succ]
      rw [mul_pow]
      ring

/-- Every finite exponential Hilbert kernel approximation converges pointwise
to the exact scalar exponential kernel. -/
theorem RealHilbertKernelFeature.exponentialPartialKernel_tendsto
    {X : Type}
    (kernel : X → X → ℝ)
    (c : ℝ)
    (x y : X) :
    Tendsto
      (fun n =>
        RealHilbertKernelFeature.exponentialPartialKernel kernel c n x y)
      atTop
      (𝓝 (Real.exp (c * kernel x y))) := by
  simp_rw [RealHilbertKernelFeature.exponentialPartialKernel_eq_sum]
  rw [tendsto_add_atTop_iff_nat
    (f := fun n =>
      ∑ m ∈ Finset.range n,
        (c * kernel x y) ^ m / (Nat.factorial m : ℝ)) 1]
  apply HasSum.tendsto_sum_nat
  rw [Real.exp_eq_exp_ℝ]
  exact expSeries_div_hasSum_exp (c * kernel x y)

/-- The concrete finite Taylor Hilbert kernels converge pointwise to the exact
one-plaquette Wilson relative kernel. -/
theorem specialUnitaryWilsonRelativeKernelPartial_tendsto
    (N : ℕ)
    (beta : ℝ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Tendsto
      (fun degree =>
        specialUnitaryWilsonRelativeKernelPartial N beta degree g h)
      atTop
      (𝓝 (specialUnitaryWilsonRelativeKernel N beta g h)) := by
  rw [specialUnitaryWilsonRelativeKernel_eq_trace]
  unfold specialUnitaryWilsonRelativeKernelPartial
  exact tendsto_const_nhds.mul
    (RealHilbertKernelFeature.exponentialPartialKernel_tendsto
      (specialUnitaryNormalizedTraceRelativeKernel N) beta g h)

/-- For nonnegative coupling, each member of the convergent sequence is already
realized by the explicit completed-tensor-product Hilbert feature constructed
in `SpecialUnitaryNormalizedTraceKernelFeature`. -/
theorem specialUnitaryWilsonRelativeKernelPartialConcrete_inner_tendsto
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Tendsto
      (fun degree =>
        inner ℝ
          ((specialUnitaryWilsonRelativeKernelPartialConcreteFeature
            N hN beta hbeta degree).feature g)
          ((specialUnitaryWilsonRelativeKernelPartialConcreteFeature
            N hN beta hbeta degree).feature h))
      atTop
      (𝓝 (specialUnitaryWilsonRelativeKernel N beta g h)) := by
  simpa only [← specialUnitaryWilsonRelativeKernelPartialConcrete_eq_inner]
    using specialUnitaryWilsonRelativeKernelPartial_tendsto N beta g h

end

end MathlibAnalytic
end MGAP4D
