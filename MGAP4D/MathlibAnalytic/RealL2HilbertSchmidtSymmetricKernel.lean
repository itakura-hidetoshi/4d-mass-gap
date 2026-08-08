import MGAP4D.MathlibAnalytic.RealL2HilbertSchmidtKernelOperator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

universe u

variable {α : Type u} [MeasurableSpace α] {μ : Measure α}

/-- A square scalar kernel representative is symmetric under product-coordinate
swap.  This formulation is deliberately representative-level, while the
operator below remains quotient-level in `L²(μ × μ)`. -/
def RealL2KernelRepresentativeSymmetric
    (k : α × α → ℝ) : Prop :=
  ∀ p : α × α, k p.swap = k p

/-- If a square real `L²` kernel admits an a.e.-equal symmetric scalar
representative, then its Hilbert--Schmidt bilinear pairing is symmetric.

The proof is exactly the product-measure swap identity.  No integrability
hypothesis beyond `K,f,g ∈ L²` is added, and no pointwise representative of the
operator output is chosen. -/
theorem realL2HilbertSchmidtKernelPairing_symmetric_of_ae_symmetric_rep
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (k : α × α → ℝ)
    (hK : (fun p => K p) =ᵐ[μ.prod μ] k)
    (hkSymm : RealL2KernelRepresentativeSymmetric k) :
    RealL2HilbertSchmidtKernelPairingSymmetric K := by
  intro f g
  have hfg := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) f g
  have hgf := realL2ExternalTensor_coeFn (μ := μ) (ν := μ) g f
  let F : α × α → ℝ := fun p => k p * (f p.1 * g p.2)
  calc
    realL2HilbertSchmidtKernelPairing K f g =
        ∫ p : α × α, k p * (f p.1 * g p.2) ∂(μ.prod μ) := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hK, hfg] with p hpK hpfg
      rw [hpK, hpfg]
      simp [realL2ExternalTensorFunction]
    _ = ∫ p : α × α, F p.swap ∂(μ.prod μ) := by
      simpa [F] using
        (MeasureTheory.integral_prod_swap (μ := μ) (ν := μ) F).symm
    _ = ∫ p : α × α, k p * (g p.1 * f p.2) ∂(μ.prod μ) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hkSymm p]
      simp [F]
      ring
    _ = realL2HilbertSchmidtKernelPairing K g f := by
      rw [realL2HilbertSchmidtKernelPairing, MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hK, hgf] with p hpK hpgf
      rw [hpK, hpgf]
      simp [realL2ExternalTensorFunction]

/-- The same representative symmetry criterion makes the associated
Fréchet--Riesz Hilbert--Schmidt operator symmetric in Mathlib's Hilbert-space
sense. -/
theorem realL2HilbertSchmidtKernelOperator_isSymmetric_of_ae_symmetric_rep
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (k : α × α → ℝ)
    (hK : (fun p => K p) =ᵐ[μ.prod μ] k)
    (hkSymm : RealL2KernelRepresentativeSymmetric k) :
    ((realL2HilbertSchmidtKernelOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric := by
  exact realL2HilbertSchmidtKernelOperator_isSymmetric K
    (realL2HilbertSchmidtKernelPairing_symmetric_of_ae_symmetric_rep
      K k hK hkSymm)

/-- Audit-visible generic symmetric-kernel bridge. -/
structure RealL2HilbertSchmidtSymmetricKernelPackage
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (k : α × α → ℝ)
    (hK : (fun p => K p) =ᵐ[μ.prod μ] k)
    (hkSymm : RealL2KernelRepresentativeSymmetric k) : Prop where
  pairingSymmetric : RealL2HilbertSchmidtKernelPairingSymmetric K
  operatorSymmetric :
    ((realL2HilbertSchmidtKernelOperator K :
      Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
      Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ).IsSymmetric

/-- Construct the generic symmetric-kernel receipt. -/
theorem realL2HilbertSchmidtSymmetricKernelPackage
    [SFinite μ]
    (K : Lp ℝ 2 (μ.prod μ))
    (k : α × α → ℝ)
    (hK : (fun p => K p) =ᵐ[μ.prod μ] k)
    (hkSymm : RealL2KernelRepresentativeSymmetric k) :
    RealL2HilbertSchmidtSymmetricKernelPackage K k hK hkSymm :=
  { pairingSymmetric :=
      realL2HilbertSchmidtKernelPairing_symmetric_of_ae_symmetric_rep
        K k hK hkSymm
    operatorSymmetric :=
      realL2HilbertSchmidtKernelOperator_isSymmetric_of_ae_symmetric_rep
        K k hK hkSymm }

end

end MathlibAnalytic
end MGAP4D
