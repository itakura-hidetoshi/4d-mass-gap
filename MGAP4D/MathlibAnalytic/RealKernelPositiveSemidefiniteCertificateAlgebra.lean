import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteRKHS
import MGAP4D.MathlibAnalytic.RealHilbertKernelFeatureAddMomentStrictness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

namespace RealKernelPositiveSemidefiniteCertificate

/-- The zero kernel is symmetric positive semidefinite. -/
noncomputable def zero
    (X : Type) :
    RealKernelPositiveSemidefiniteCertificate X (fun _ _ => 0) := by
  let C := RealHilbertKernelFeature.nonnegSMul
    0 (by positivity) (RealHilbertKernelFeature.one X)
  simpa using C.toPositiveSemidefiniteCertificate

/-- Sums of symmetric positive-semidefinite kernels remain symmetric positive semidefinite. -/
noncomputable def add
    {X : Type}
    {kernel₁ kernel₂ : X → X → ℝ}
    (C₁ : RealKernelPositiveSemidefiniteCertificate X kernel₁)
    (C₂ : RealKernelPositiveSemidefiniteCertificate X kernel₂) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y => kernel₁ x y + kernel₂ x y) :=
  (RealHilbertKernelFeature.add C₁.toHilbertFeature C₂.toHilbertFeature).toPositiveSemidefiniteCertificate

/-- Multiplication by a nonnegative scalar preserves a symmetric PSD kernel. -/
noncomputable def nonnegSMul
    {X : Type}
    {kernel : X → X → ℝ}
    (c : ℝ)
    (hc : 0 ≤ c)
    (C : RealKernelPositiveSemidefiniteCertificate X kernel) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y => c * kernel x y) :=
  (RealHilbertKernelFeature.nonnegSMul c hc C.toHilbertFeature).toPositiveSemidefiniteCertificate

/-- The Schur product of two symmetric PSD kernels is symmetric PSD.  The
proof is the Hilbert tensor-product realization rather than a matrix-level
Schur-product argument. -/
noncomputable def mul
    {X : Type}
    {kernel₁ kernel₂ : X → X → ℝ}
    (C₁ : RealKernelPositiveSemidefiniteCertificate X kernel₁)
    (C₂ : RealKernelPositiveSemidefiniteCertificate X kernel₂) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y => kernel₁ x y * kernel₂ x y) :=
  (RealHilbertKernelFeature.mul C₁.toHilbertFeature C₂.toHilbertFeature).toPositiveSemidefiniteCertificate

/-- Pullback along an arbitrary map preserves the symmetric PSD certificate. -/
noncomputable def comap
    {X Y : Type}
    {kernel : Y → Y → ℝ}
    (C : RealKernelPositiveSemidefiniteCertificate Y kernel)
    (f : X → Y) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y => kernel (f x) (f y)) :=
  (C.toHilbertFeature.comap f).toPositiveSemidefiniteCertificate

/-- Any finite sum of symmetric PSD kernels is symmetric PSD. -/
theorem finsetSum
    {X ι : Type}
    (s : Finset ι)
    (kernel : ι → X → X → ℝ)
    (C : ∀ i ∈ s, RealKernelPositiveSemidefiniteCertificate X (kernel i)) :
    RealKernelPositiveSemidefiniteCertificate X
      (fun x y => ∑ i ∈ s, kernel i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using RealKernelPositiveSemidefiniteCertificate.zero X
  | @insert a s ha ih =>
      have Ca : RealKernelPositiveSemidefiniteCertificate X (kernel a) :=
        C a (by simp)
      have Cs : RealKernelPositiveSemidefiniteCertificate X
          (fun x y => ∑ i ∈ s, kernel i x y) :=
        ih (fun i hi => C i (by simp [hi]))
      simpa [Finset.sum_insert, ha] using Ca.add Cs

/-- Symmetric positive semidefiniteness is closed under pointwise limits.

This is the kernel-level closure principle used below for an exact Wilson
remainder after one Taylor sector has been removed.  It is deliberately proved
at the finite Gram level: every finite quadratic form converges termwise, and
the nonnegative real half-line is closed. -/
theorem pointwiseLimit
    {X : Type}
    {kernel : ℕ → X → X → ℝ}
    {limitKernel : X → X → ℝ}
    (C : ∀ n, RealKernelPositiveSemidefiniteCertificate X (kernel n))
    (hlimit : ∀ x y,
      Tendsto (fun n => kernel n x y) atTop (𝓝 (limitKernel x y))) :
    RealKernelPositiveSemidefiniteCertificate X limitKernel := by
  refine ⟨?_, ?_⟩
  · intro x y
    have hxy := hlimit x y
    have hyx := hlimit y x
    have heq :
        (fun n => kernel n x y) =ᶠ[atTop]
          (fun n => kernel n y x) :=
      Filter.Eventually.of_forall fun n => (C n).symmetric x y
    exact tendsto_nhds_unique hxy (hyx.congr' heq.symm)
  · intro ι _ points coefficients
    let quadratic : ℕ → ℝ := fun n =>
      ∑ p : ι × ι,
        coefficients p.1 * coefficients p.2 *
          kernel n (points p.1) (points p.2)
    let limitQuadratic : ℝ :=
      ∑ p : ι × ι,
        coefficients p.1 * coefficients p.2 *
          limitKernel (points p.1) (points p.2)
    have hTerm : ∀ p : ι × ι,
        Tendsto
          (fun n =>
            coefficients p.1 * coefficients p.2 *
              kernel n (points p.1) (points p.2))
          atTop
          (𝓝
            (coefficients p.1 * coefficients p.2 *
              limitKernel (points p.1) (points p.2))) := by
      intro p
      exact tendsto_const_nhds.mul
        (hlimit (points p.1) (points p.2))
    have hQuadratic : Tendsto quadratic atTop (𝓝 limitQuadratic) := by
      exact tendsto_fintype_sum_real
        (fun n (p : ι × ι) =>
          coefficients p.1 * coefficients p.2 *
            kernel n (points p.1) (points p.2))
        (fun p : ι × ι =>
          coefficients p.1 * coefficients p.2 *
            limitKernel (points p.1) (points p.2))
        hTerm
    have hNonneg : ∀ n, 0 ≤ quadratic n := by
      intro n
      dsimp [quadratic]
      rw [Fintype.sum_prod_type]
      exact (C n).positiveSemidefinite ι points coefficients
    have hLimitNonneg : 0 ≤ limitQuadratic :=
      ge_of_tendsto hQuadratic (Filter.Eventually.of_forall hNonneg)
    dsimp [limitQuadratic] at hLimitNonneg
    rw [Fintype.sum_prod_type] at hLimitNonneg
    exact hLimitNonneg

end RealKernelPositiveSemidefiniteCertificate

end

end MathlibAnalytic
end MGAP4D
