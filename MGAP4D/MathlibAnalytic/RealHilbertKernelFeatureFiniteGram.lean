import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureProduct

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A real scalar kernel is positive semidefinite when every finite Gram
quadratic form with real coefficients is nonnegative. -/
def RealKernelPositiveSemidefinite
    (X : Type)
    (kernel : X → X → ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι]
    (points : ι → X)
    (coefficients : ι → ℝ),
      0 ≤ ∑ i : ι, ∑ j : ι,
        coefficients i * coefficients j * kernel (points i) (points j)

/-- Every kernel represented by a real Hilbert inner product is symmetric. -/
theorem RealHilbertKernelFeature.symmetric
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (x y : X) :
    kernel x y = kernel y x := by
  rw [C.kernel_eq_inner, C.kernel_eq_inner, real_inner_comm]

/-- Every real Hilbert feature realization generates a positive-semidefinite
kernel.  The finite Gram quadratic form is the squared norm of the weighted
sum of feature vectors. -/
theorem RealHilbertKernelFeature.positiveSemidefinite
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel) :
    RealKernelPositiveSemidefinite X kernel := by
  intro ι _ points coefficients
  let weightedFeatureSum : C.FeatureHilbert :=
    ∑ i : ι, coefficients i • C.feature (points i)
  have hGram :
      inner ℝ weightedFeatureSum weightedFeatureSum =
        ∑ i : ι, ∑ j : ι,
          coefficients i * coefficients j *
            kernel (points i) (points j) := by
    simp only [weightedFeatureSum, sum_inner, inner_sum,
      real_inner_smul_left, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [← C.kernel_eq_inner]
    rw [C.symmetric (points j) (points i)]
  rw [← hGram]
  exact real_inner_self_nonneg

/-- The concrete Gram identity associated with a Hilbert feature certificate. -/
theorem RealHilbertKernelFeature.finiteGram_eq_inner
    {X ι : Type}
    [Fintype ι]
    {kernel : X → X → ℝ}
    (C : RealHilbertKernelFeature X kernel)
    (points : ι → X)
    (coefficients : ι → ℝ) :
    (∑ i : ι, ∑ j : ι,
        coefficients i * coefficients j * kernel (points i) (points j)) =
      inner ℝ
        (∑ i : ι, coefficients i • C.feature (points i))
        (∑ i : ι, coefficients i • C.feature (points i)) := by
  symm
  simp only [sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [← C.kernel_eq_inner]
  rw [C.symmetric (points j) (points i)]

end

end MathlibAnalytic
end MGAP4D
