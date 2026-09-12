import MGAP4D.MathlibAnalytic.FiniteOSGramKernelProductClosure

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pull a finite nonnegative Gram kernel back along an arbitrary map of finite
configuration carriers. -/
def FiniteOSGramKernelOn.comap
    {α β : Type} [Fintype α] [Fintype β]
    (K : FiniteOSGramKernelOn α)
    (f : β → α) :
    FiniteOSGramKernelOn β :=
  { Feature := K.Feature
    kernel := fun x y => K.kernel (f x) (f y)
    coefficient := K.coefficient
    coefficient_nonneg := K.coefficient_nonneg
    feature := fun k x => K.feature k (f x)
    kernel_decomposition := by
      intro x y
      exact K.kernel_decomposition (f x) (f y) }

@[simp] theorem finiteOSGramKernelOn_comap_apply
    {α β : Type} [Fintype α] [Fintype β]
    (K : FiniteOSGramKernelOn α)
    (f : β → α)
    (x y : β) :
    (K.comap f).kernel x y = K.kernel (f x) (f y) :=
  rfl

/-- Comap preserves finite reflection positivity. -/
theorem finiteOSGramKernelOn_comap_reflectionPositive
    {α β : Type} [Fintype α] [Fintype β]
    (K : FiniteOSGramKernelOn α)
    (f : β → α) :
    FiniteOSReflectionPositive (K.comap f).toCertificate :=
  finite_os_gram_certificate_reflectionPositive (K.comap f).toCertificate

end

end MathlibAnalytic
end MGAP4D
