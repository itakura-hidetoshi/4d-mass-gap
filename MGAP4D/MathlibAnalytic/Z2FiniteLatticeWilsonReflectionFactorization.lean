import MGAP4D.MathlibAnalytic.Z2FiniteLatticeWilsonSystem
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticGramBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pull a finite Gram kernel back along an arbitrary map of positive-time
configuration spaces. -/
def FiniteOSGramKernelOn.pullback
    {α β : Type} [Fintype α] [Fintype β]
    (K : FiniteOSGramKernelOn β)
    (f : α → β) :
    FiniteOSGramKernelOn α :=
  { Feature := K.Feature
    kernel := fun x y => K.kernel (f x) (f y)
    coefficient := K.coefficient
    coefficient_nonneg := K.coefficient_nonneg
    feature := fun k x => K.feature k (f x)
    kernel_decomposition := by
      intro x y
      exact K.kernel_decomposition (f x) (f y) }

@[simp]
theorem finite_os_gram_kernel_pullback_apply
    {α β : Type} [Fintype α] [Fintype β]
    (K : FiniteOSGramKernelOn β)
    (f : α → β) (x y : α) :
    (K.pullback f).kernel x y = K.kernel (f x) (f y) :=
  rfl

/-- Pullback preserves finite OS reflection positivity. -/
theorem finite_os_gram_kernel_pullback_reflectionPositive
    {α β : Type} [Fintype α] [Fintype β]
    (K : FiniteOSGramKernelOn β)
    (f : α → β) :
    FiniteOSReflectionPositive (K.pullback f).toCertificate :=
  finite_os_gram_certificate_reflectionPositive (K.pullback f).toCertificate

/-- Reflection-factorization data for an actual finite-lattice Wilson system
whose crossing-plane factors are explicit local `Z₂` Wilson kernels.

The list `crossingVariables` records the `Z₂` boundary variable contributed by
each plaquette crossing the reflection plane.  The factorization field is the
remaining lattice-geometric identity: the full reflected Wilson weight equals
a positive-half factor, the product of all local crossing kernels, and its
reflected partner. -/
structure Z2FiniteLatticeWilsonReflectionFactorization
    (L : FiniteLatticeWilsonSystem) where
  PositiveConfiguration : Type
  [positiveFintype : Fintype PositiveConfiguration]
  [positiveInhabited : Inhabited PositiveConfiguration]
  assemble : PositiveConfiguration → PositiveConfiguration → L.Configuration
  reflection : L.Configuration → L.Configuration
  reflection_involutive : Function.Involutive reflection
  reflection_assemble :
    ∀ x y, reflection (assemble x y) = assemble y x
  energyIdentity : ℝ
  energyNontrivial : ℝ
  energy_order : energyIdentity ≤ energyNontrivial
  crossingVariables : List (PositiveConfiguration → Z2Gauge)
  halfSpaceFactor : PositiveConfiguration → ℝ
  wilson_weight_factorization :
    ∀ x y,
      Real.exp (-L.beta * L.wilsonAction (assemble x y)) =
        halfSpaceFactor x *
          ((crossingVariables.map fun q =>
            (z2GaugeWilsonPlaquetteGramKernel
              L.beta energyIdentity energyNontrivial
              L.beta_nonneg energy_order).kernel (q x) (q y)).prod) *
          halfSpaceFactor y

attribute [instance]
  Z2FiniteLatticeWilsonReflectionFactorization.positiveFintype
  Z2FiniteLatticeWilsonReflectionFactorization.positiveInhabited

/-- The local Gram kernel attached to one crossing-plane boundary variable. -/
def Z2FiniteLatticeWilsonReflectionFactorization.localKernel
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonReflectionFactorization L)
    (q : D.PositiveConfiguration → Z2Gauge) :
    FiniteOSGramKernelOn D.PositiveConfiguration :=
  (z2GaugeWilsonPlaquetteGramKernel
    L.beta D.energyIdentity D.energyNontrivial
    L.beta_nonneg D.energy_order).pullback q

/-- The list of all local crossing-plane Gram kernels. -/
def Z2FiniteLatticeWilsonReflectionFactorization.crossingKernels
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonReflectionFactorization L) :
    List (FiniteOSGramKernelOn D.PositiveConfiguration) :=
  D.crossingVariables.map D.localKernel

/-- Full reflected Gram kernel: product of crossing kernels, sandwiched by the
same-side half-space factor. -/
def Z2FiniteLatticeWilsonReflectionFactorization.fullGramKernel
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonReflectionFactorization L) :
    FiniteOSGramKernelOn D.PositiveConfiguration :=
  (FiniteOSGramKernelOn.listProduct D.crossingKernels).sandwich
    D.halfSpaceFactor

/-- The constructed full Gram kernel is exactly the finite-volume Wilson
Boltzmann kernel supplied by the reflection factorization. -/
theorem z2_finite_lattice_fullGramKernel_eq_wilson_weight
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonReflectionFactorization L)
    (x y : D.PositiveConfiguration) :
    D.fullGramKernel.kernel x y =
      Real.exp (-L.beta * L.wilsonAction (D.assemble x y)) := by
  rw [D.wilson_weight_factorization x y]
  simp only [Z2FiniteLatticeWilsonReflectionFactorization.fullGramKernel,
    finite_os_gram_kernel_sandwich_apply,
    Z2FiniteLatticeWilsonReflectionFactorization.crossingKernels,
    finite_os_gram_kernel_listProduct_apply]
  congr 2
  induction D.crossingVariables with
  | nil => rfl
  | cons q qs ih =>
      simp [Z2FiniteLatticeWilsonReflectionFactorization.localKernel, ih]

/-- Build the repository's Wilson reflection certificate directly from the
`Z₂` lattice factorization. -/
def Z2FiniteLatticeWilsonReflectionFactorization.toReflectionCertificate
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonReflectionFactorization L) :
    FiniteLatticeWilsonOSReflectionCertificate L :=
  { PositiveConfiguration := D.PositiveConfiguration
    assemble := D.assemble
    reflection := D.reflection
    reflection_involutive := D.reflection_involutive
    reflection_assemble := D.reflection_assemble
    kernel := D.fullGramKernel.kernel
    kernel_eq_wilson_weight :=
      z2_finite_lattice_fullGramKernel_eq_wilson_weight D
    gram := D.fullGramKernel.toCertificate
    positiveConfigurationEquiv := Equiv.refl D.PositiveConfiguration
    gram_kernel_agrees := by
      intro x y
      rfl }

/-- The full finite-lattice `Z₂` Wilson kernel is OS reflection positive once
the explicit geometric factorization has been supplied. -/
theorem z2_finite_lattice_wilson_reflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (D : Z2FiniteLatticeWilsonReflectionFactorization L) :
    FiniteLatticeWilsonOSReflectionPositive D.toReflectionCertificate :=
  finite_lattice_wilson_os_reflection_positive_of_certificate
    D.toReflectionCertificate

/-- Audit-visible complete finite-volume OS certificate generated from the
`Z₂` reflection factorization. -/
def z2FiniteLatticeWilsonOSCertificate
    (L : FiniteLatticeWilsonSystem)
    (D : Z2FiniteLatticeWilsonReflectionFactorization L) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  finiteWilsonOSReflectionPositivityCertificateOfReflectionData
    L D.toReflectionCertificate

end

end MathlibAnalytic
end MGAP4D
