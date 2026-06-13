import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticGramBridge
import Mathlib.Data.Fintype.BigOperators

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A nonnegative finite Gram kernel on a fixed positive-time configuration
space.  Fixing the carrier makes closure under pointwise products transparent. -/
structure FiniteOSGramKernelOn
    (α : Type) [Fintype α] where
  Feature : Type
  [featureFintype : Fintype Feature]
  kernel : α → α → ℝ
  coefficient : Feature → ℝ
  coefficient_nonneg : ∀ k, 0 ≤ coefficient k
  feature : Feature → α → ℝ
  kernel_decomposition :
    ∀ x y,
      kernel x y =
        ∑ k : Feature,
          coefficient k * feature k x * feature k y

attribute [instance] FiniteOSGramKernelOn.featureFintype

/-- Forget the fixed carrier and recover the repository's general OS Gram
certificate. -/
def FiniteOSGramKernelOn.toCertificate
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α) :
    FiniteOSReflectionGramCertificate :=
  { PositiveConfiguration := α
    Feature := K.Feature
    kernel := K.kernel
    coefficient := K.coefficient
    coefficient_nonneg := K.coefficient_nonneg
    feature := K.feature
    kernel_decomposition := K.kernel_decomposition }

/-- The constant-one kernel is a Gram kernel with one feature. -/
def FiniteOSGramKernelOn.one
    (α : Type) [Fintype α] :
    FiniteOSGramKernelOn α :=
  { Feature := PUnit
    kernel := fun _x _y => 1
    coefficient := fun _ => 1
    coefficient_nonneg := fun _ => zero_le_one
    feature := fun _ _x => 1
    kernel_decomposition := by
      intro x y
      simp }

/-- Pointwise products of finite nonnegative Gram kernels are again finite
nonnegative Gram kernels.  The new feature space is the product of the two
feature spaces and the new coefficients are products of nonnegative
coefficients. -/
def FiniteOSGramKernelOn.mul
    {α : Type} [Fintype α]
    (K L : FiniteOSGramKernelOn α) :
    FiniteOSGramKernelOn α :=
  { Feature := K.Feature × L.Feature
    kernel := fun x y => K.kernel x y * L.kernel x y
    coefficient := fun p => K.coefficient p.1 * L.coefficient p.2
    coefficient_nonneg := fun p =>
      mul_nonneg (K.coefficient_nonneg p.1) (L.coefficient_nonneg p.2)
    feature := fun p x => K.feature p.1 x * L.feature p.2 x
    kernel_decomposition := by
      intro x y
      rw [K.kernel_decomposition, L.kernel_decomposition,
        Fintype.sum_mul_sum, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro k _hk
      apply Finset.sum_congr rfl
      intro l _hl
      ring }

@[simp]
theorem finite_os_gram_kernel_mul_apply
    {α : Type} [Fintype α]
    (K L : FiniteOSGramKernelOn α) (x y : α) :
    (K.mul L).kernel x y = K.kernel x y * L.kernel x y :=
  rfl

/-- Reflection positivity is closed under pointwise products of Gram kernels. -/
theorem finite_os_gram_kernel_mul_reflectionPositive
    {α : Type} [Fintype α]
    (K L : FiniteOSGramKernelOn α) :
    FiniteOSReflectionPositive (K.mul L).toCertificate :=
  finite_os_gram_certificate_reflectionPositive (K.mul L).toCertificate

/-- Multiplying the kernel by one factor from each half-space preserves the
Gram form.  In OS terminology this absorbs action terms supported strictly on
the positive and negative sides of the reflection plane into the observable. -/
def FiniteOSGramKernelOn.sandwich
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (a : α → ℝ) :
    FiniteOSGramKernelOn α :=
  { Feature := K.Feature
    kernel := fun x y => a x * K.kernel x y * a y
    coefficient := K.coefficient
    coefficient_nonneg := K.coefficient_nonneg
    feature := fun k x => a x * K.feature k x
    kernel_decomposition := by
      intro x y
      rw [K.kernel_decomposition]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      ring }

@[simp]
theorem finite_os_gram_kernel_sandwich_apply
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (a : α → ℝ) (x y : α) :
    (K.sandwich a).kernel x y = a x * K.kernel x y * a y :=
  rfl

/-- Same-side factors preserve reflection positivity. -/
theorem finite_os_gram_kernel_sandwich_reflectionPositive
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (a : α → ℝ) :
    FiniteOSReflectionPositive (K.sandwich a).toCertificate :=
  finite_os_gram_certificate_reflectionPositive (K.sandwich a).toCertificate

/-- Finite products of crossing-plane kernels, built recursively from the
constant-one kernel and binary product closure. -/
def FiniteOSGramKernelOn.listProduct
    {α : Type} [Fintype α] :
    List (FiniteOSGramKernelOn α) → FiniteOSGramKernelOn α
  | [] => FiniteOSGramKernelOn.one α
  | K :: Ks => K.mul (FiniteOSGramKernelOn.listProduct Ks)

@[simp]
theorem finite_os_gram_kernel_listProduct_nil
    {α : Type} [Fintype α] :
    FiniteOSGramKernelOn.listProduct ([] : List (FiniteOSGramKernelOn α)) =
      FiniteOSGramKernelOn.one α :=
  rfl

@[simp]
theorem finite_os_gram_kernel_listProduct_cons
    {α : Type} [Fintype α]
    (K : FiniteOSGramKernelOn α)
    (Ks : List (FiniteOSGramKernelOn α)) :
    FiniteOSGramKernelOn.listProduct (K :: Ks) =
      K.mul (FiniteOSGramKernelOn.listProduct Ks) :=
  rfl

/-- The aggregate kernel is exactly the pointwise product of the individual
crossing kernels. -/
theorem finite_os_gram_kernel_listProduct_apply
    {α : Type} [Fintype α]
    (Ks : List (FiniteOSGramKernelOn α)) (x y : α) :
    (FiniteOSGramKernelOn.listProduct Ks).kernel x y =
      (Ks.map fun K => K.kernel x y).prod := by
  induction Ks with
  | nil => simp [FiniteOSGramKernelOn.listProduct, FiniteOSGramKernelOn.one]
  | cons K Ks ih =>
      simp [FiniteOSGramKernelOn.listProduct, FiniteOSGramKernelOn.mul, ih]

/-- Any finite product of crossing-plane Gram kernels is OS reflection
positive. -/
theorem finite_os_gram_kernel_listProduct_reflectionPositive
    {α : Type} [Fintype α]
    (Ks : List (FiniteOSGramKernelOn α)) :
    FiniteOSReflectionPositive
      (FiniteOSGramKernelOn.listProduct Ks).toCertificate :=
  finite_os_gram_certificate_reflectionPositive
    (FiniteOSGramKernelOn.listProduct Ks).toCertificate

/-- Finite crossing-kernel products remain reflection positive after absorption
of arbitrary real half-space factors. -/
theorem finite_os_crossing_product_with_halfspace_factor_reflectionPositive
    {α : Type} [Fintype α]
    (Ks : List (FiniteOSGramKernelOn α))
    (a : α → ℝ) :
    FiniteOSReflectionPositive
      ((FiniteOSGramKernelOn.listProduct Ks).sandwich a).toCertificate :=
  finite_os_gram_kernel_sandwich_reflectionPositive
    (FiniteOSGramKernelOn.listProduct Ks) a

end

end MathlibAnalytic
end MGAP4D
