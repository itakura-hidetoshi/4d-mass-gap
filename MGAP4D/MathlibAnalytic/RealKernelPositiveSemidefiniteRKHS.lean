import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefiniteCertificate
import Mathlib.Analysis.InnerProductSpace.Reproducing

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The real one-dimensional inner product is ordinary multiplication. -/
private theorem real_inner_eq_mul (x y : ℝ) :
    inner ℝ x y = x * y := by
  change star x * y = x * y
  rw [star_trivial]

/-- Turn a real scalar kernel into an operator-valued kernel on the
one-dimensional real Hilbert space. -/
def RealKernelPositiveSemidefiniteCertificate.operatorKernel
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealKernelPositiveSemidefiniteCertificate X kernel) :
    Matrix X X (ℝ →L[ℝ] ℝ) :=
  fun x y => kernel x y • (1 : ℝ →L[ℝ] ℝ)

/-- The operator-valued lift of a symmetric scalar kernel is Hermitian. -/
theorem RealKernelPositiveSemidefiniteCertificate.operatorKernel_isHermitian
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealKernelPositiveSemidefiniteCertificate X kernel) :
    C.operatorKernel.IsHermitian := by
  ext x y
  change kernel x y * ((star (1 : ℝ →L[ℝ] ℝ)) 1) = kernel y x
  rw [star_one]
  simpa [C.symmetric x y]

/-- The operator-valued lift of a symmetric positive-semidefinite scalar
kernel is positive semidefinite in the sense required by `RKHS.OfKernel`. -/
theorem RealKernelPositiveSemidefiniteCertificate.operatorKernel_posSemidef
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealKernelPositiveSemidefiniteCertificate X kernel) :
    C.operatorKernel.PosSemidef := by
  refine ((RKHS.posSemidef_tfae
    (𝕜 := ℝ) (X := X) (V := ℝ) (K := C.operatorKernel)).out 2 0).mp ?_
  refine ⟨C.operatorKernel_isHermitian, ?_⟩
  intro coefficients
  classical
  have hFinite := C.positiveSemidefinite
    {x // x ∈ coefficients.support}
    (fun x => x.1)
    (fun x => coefficients x.1)
  simpa [RealKernelPositiveSemidefiniteCertificate.operatorKernel,
    Finsupp.sum, real_inner_eq_mul,
    ← Finset.sum_attach coefficients.support,
    C.symmetric, mul_comm, mul_left_comm, mul_assoc]
    using hFinite

/-- Moore--Aronszajn realization of a symmetric positive-semidefinite real
kernel, using mathlib's `RKHS.OfKernel` completion. -/
noncomputable def RealKernelPositiveSemidefiniteCertificate.toHilbertFeature
    {X : Type}
    {kernel : X → X → ℝ}
    (C : RealKernelPositiveSemidefiniteCertificate X kernel) :
    RealHilbertKernelFeature X kernel := by
  let K := C.operatorKernel
  letI : Fact K.PosSemidef := ⟨C.operatorKernel_posSemidef⟩
  refine
    { FeatureHilbert := RKHS.OfKernel K
      feature := fun x => RKHS.kerFun (RKHS.OfKernel K) x (1 : ℝ)
      kernel_eq_inner := ?_ }
  intro x y
  have hKernel :=
    RKHS.kernel_inner (H := RKHS.OfKernel K) y x (1 : ℝ) (1 : ℝ)
  rw [← hKernel]
  simp [K, RealKernelPositiveSemidefiniteCertificate.operatorKernel,
    C.symmetric, real_inner_eq_mul]

end

end MathlibAnalytic
end MGAP4D
