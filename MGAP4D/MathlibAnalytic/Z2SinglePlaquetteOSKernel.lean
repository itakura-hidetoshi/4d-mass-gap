import MGAP4D.MathlibAnalytic.FiniteOSGramKernelProductClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The two real characters of the two-element group, represented on `Bool`.
`false` is the trivial mode and `true` is the sign mode. -/
def z2RealCharacter (mode x : Bool) : ℝ :=
  if mode then (if x then -1 else 1) else 1

/-- Fourier coefficients of the symmetric two-point kernel with diagonal value
`w₀` and off-diagonal value `w₁`. -/
def z2KernelCoefficient (w₀ w₁ : ℝ) (mode : Bool) : ℝ :=
  if mode then (w₀ - w₁) / 2 else (w₀ + w₁) / 2

/-- Translation-invariant two-point kernel, identified with the local `Z₂`
plaquette kernel. -/
def z2PlaquetteKernel (w₀ w₁ : ℝ) (x y : Bool) : ℝ :=
  if x = y then w₀ else w₁

/-- Explicit two-character Fourier decomposition of the `Z₂` kernel. -/
theorem z2PlaquetteKernel_fourier_decomposition
    (w₀ w₁ : ℝ) (x y : Bool) :
    z2PlaquetteKernel w₀ w₁ x y =
      ∑ mode : Bool,
        z2KernelCoefficient w₀ w₁ mode *
          z2RealCharacter mode x * z2RealCharacter mode y := by
  cases x <;> cases y <;>
    norm_num [z2PlaquetteKernel, z2KernelCoefficient, z2RealCharacter]

/-- The trivial Fourier coefficient is nonnegative when both kernel values are
nonnegative. -/
theorem z2KernelCoefficient_trivial_nonneg
    {w₀ w₁ : ℝ} (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) :
    0 ≤ z2KernelCoefficient w₀ w₁ false := by
  simp [z2KernelCoefficient]
  linarith

/-- The sign Fourier coefficient is nonnegative exactly under the natural
ordering `w₁ ≤ w₀`. -/
theorem z2KernelCoefficient_sign_nonneg
    {w₀ w₁ : ℝ} (horder : w₁ ≤ w₀) :
    0 ≤ z2KernelCoefficient w₀ w₁ true := by
  simp [z2KernelCoefficient]
  linarith

/-- Explicit nonnegative Gram kernel for the two-element plaquette weight. -/
def z2PlaquetteGramKernel
    (w₀ w₁ : ℝ)
    (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (horder : w₁ ≤ w₀) :
    FiniteOSGramKernelOn Bool :=
  { Feature := Bool
    kernel := z2PlaquetteKernel w₀ w₁
    coefficient := z2KernelCoefficient w₀ w₁
    coefficient_nonneg := by
      intro mode
      cases mode
      · exact z2KernelCoefficient_trivial_nonneg hw₀ hw₁
      · exact z2KernelCoefficient_sign_nonneg horder
    feature := z2RealCharacter
    kernel_decomposition :=
      z2PlaquetteKernel_fourier_decomposition w₀ w₁ }

/-- The two-point kernel is OS reflection positive whenever
`0 ≤ w₁ ≤ w₀`. -/
theorem z2PlaquetteKernel_reflectionPositive
    (w₀ w₁ : ℝ)
    (hw₀ : 0 ≤ w₀) (hw₁ : 0 ≤ w₁) (horder : w₁ ≤ w₀) :
    FiniteOSReflectionPositive
      (z2PlaquetteGramKernel w₀ w₁ hw₀ hw₁ horder).toCertificate :=
  finite_os_gram_certificate_reflectionPositive
    (z2PlaquetteGramKernel w₀ w₁ hw₀ hw₁ horder).toCertificate

/-- `Z₂` Wilson-type Boltzmann values at the identity and nontrivial element. -/
def z2WilsonWeightIdentity (β energyIdentity : ℝ) : ℝ :=
  Real.exp (-β * energyIdentity)

def z2WilsonWeightNontrivial (β energyNontrivial : ℝ) : ℝ :=
  Real.exp (-β * energyNontrivial)

/-- Both local Wilson Boltzmann values are positive. -/
theorem z2WilsonWeightIdentity_pos (β energyIdentity : ℝ) :
    0 < z2WilsonWeightIdentity β energyIdentity :=
  Real.exp_pos _

theorem z2WilsonWeightNontrivial_pos (β energyNontrivial : ℝ) :
    0 < z2WilsonWeightNontrivial β energyNontrivial :=
  Real.exp_pos _

/-- If the inverse temperature is nonnegative and the identity minimizes the
plaquette energy, then the nontrivial Boltzmann value does not exceed the
identity value. -/
theorem z2WilsonWeightNontrivial_le_identity
    {β energyIdentity energyNontrivial : ℝ}
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial) :
    z2WilsonWeightNontrivial β energyNontrivial ≤
      z2WilsonWeightIdentity β energyIdentity := by
  unfold z2WilsonWeightNontrivial z2WilsonWeightIdentity
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Concrete local `Z₂` Wilson Gram kernel. -/
def z2WilsonPlaquetteGramKernel
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSGramKernelOn Bool :=
  z2PlaquetteGramKernel
    (z2WilsonWeightIdentity β energyIdentity)
    (z2WilsonWeightNontrivial β energyNontrivial)
    (z2WilsonWeightIdentity_pos β energyIdentity).le
    (z2WilsonWeightNontrivial_pos β energyNontrivial).le
    (z2WilsonWeightNontrivial_le_identity hβ hEnergy)

/-- Fully explicit single-plaquette Osterwalder--Schrader positivity for the
`Z₂` Wilson-type weight. -/
theorem z2Wilson_singlePlaquette_reflectionPositive
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteOSReflectionPositive
      (z2WilsonPlaquetteGramKernel
        β energyIdentity energyNontrivial hβ hEnergy).toCertificate :=
  finite_os_gram_certificate_reflectionPositive
    (z2WilsonPlaquetteGramKernel
      β energyIdentity energyNontrivial hβ hEnergy).toCertificate

/-- Any finite product of the explicit `Z₂` crossing-plaquette kernels is OS
reflection positive. -/
theorem z2Wilson_crossingPlaquettes_reflectionPositive
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) :
    FiniteOSReflectionPositive
      (FiniteOSGramKernelOn.listProduct
        (List.replicate n
          (z2WilsonPlaquetteGramKernel
            β energyIdentity energyNontrivial hβ hEnergy))).toCertificate :=
  finite_os_gram_kernel_listProduct_reflectionPositive _

/-- Same-side action factors may be absorbed after taking any finite product of
explicit `Z₂` crossing kernels. -/
theorem z2Wilson_fullReflectionKernel_reflectionPositive
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial)
    (n : ℕ) (a : Bool → ℝ) :
    FiniteOSReflectionPositive
      ((FiniteOSGramKernelOn.listProduct
        (List.replicate n
          (z2WilsonPlaquetteGramKernel
            β energyIdentity energyNontrivial hβ hEnergy))).sandwich a)
        .toCertificate :=
  finite_os_crossing_product_with_halfspace_factor_reflectionPositive _ a

end

end MathlibAnalytic
end MGAP4D
