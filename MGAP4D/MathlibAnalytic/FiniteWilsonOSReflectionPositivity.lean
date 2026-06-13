import MGAP4D.MathlibAnalytic.CompactGaugeWilsonGaugeInvariance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Time reflection on a pair of negative/positive half-lattice configurations. -/
def osPairReflection {α : Type} (p : α × α) : α × α := (p.2, p.1)

/-- Pair reflection is an involution. -/
theorem osPairReflection_involutive {α : Type} :
    Function.Involutive (@osPairReflection α) := by
  rintro ⟨x, y⟩
  rfl

/-- A finite reflection kernel together with an explicit nonnegative Gram
factorization.

For a positive-time observable `F`, the OS form is
`∑ x,y, F x K(x,y) F y`.  In lattice gauge theory, the feature index is
supplied by the character/Peter--Weyl expansion of plaquettes crossing the
reflection plane. -/
structure FiniteOSReflectionGramCertificate where
  PositiveConfiguration : Type
  [positiveFintype : Fintype PositiveConfiguration]
  Feature : Type
  [featureFintype : Fintype Feature]
  kernel : PositiveConfiguration → PositiveConfiguration → ℝ
  coefficient : Feature → ℝ
  coefficient_nonneg : ∀ k, 0 ≤ coefficient k
  feature : Feature → PositiveConfiguration → ℝ
  kernel_decomposition :
    ∀ x y,
      kernel x y =
        ∑ k : Feature, coefficient k * feature k x * feature k y

attribute [instance]
  FiniteOSReflectionGramCertificate.positiveFintype
  FiniteOSReflectionGramCertificate.featureFintype

/-- The finite-sum algebra behind reflection positivity: a kernel with a Gram
expansion has a quadratic form equal to a weighted sum of squares. -/
theorem finite_gram_quadratic_identity
    {α κ : Type} [Fintype α] [Fintype κ]
    (coefficient : κ → ℝ) (feature : κ → α → ℝ)
    (F : α → ℝ) :
    (∑ x : α, ∑ y : α,
      F x * (∑ k : κ, coefficient k * feature k x * feature k y) * F y) =
    ∑ k : κ, coefficient k * (∑ x : α, F x * feature k x) ^ 2 := by
  classical
  calc
    (∑ x : α, ∑ y : α,
      F x * (∑ k : κ, coefficient k * feature k x * feature k y) * F y) =
        ∑ x : α, ∑ y : α, ∑ k : κ,
          coefficient k * (F x * feature k x) * (F y * feature k y) := by
            apply Finset.sum_congr rfl
            intro x _hx
            apply Finset.sum_congr rfl
            intro y _hy
            rw [Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
    _ = ∑ x : α, ∑ k : κ, ∑ y : α,
          coefficient k * (F x * feature k x) * (F y * feature k y) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [Finset.sum_comm]
    _ = ∑ k : κ, ∑ x : α, ∑ y : α,
          coefficient k * (F x * feature k x) * (F y * feature k y) := by
            rw [Finset.sum_comm]
    _ = ∑ k : κ, coefficient k * (∑ x : α, F x * feature k x) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [pow_two]
            calc
              (∑ x : α, ∑ y : α,
                coefficient k * (F x * feature k x) *
                  (F y * feature k y)) =
                  ∑ x : α,
                    (coefficient k * (F x * feature k x)) *
                      (∑ y : α, F y * feature k y) := by
                        apply Finset.sum_congr rfl
                        intro x _hx
                        rw [← Finset.mul_sum]
              _ = (∑ x : α, coefficient k * (F x * feature k x)) *
                    (∑ y : α, F y * feature k y) := by
                      rw [← Finset.sum_mul]
              _ = (coefficient k * (∑ x : α, F x * feature k x)) *
                    (∑ y : α, F y * feature k y) := by
                      rw [← Finset.mul_sum]
              _ = coefficient k *
                    ((∑ x : α, F x * feature k x) *
                      (∑ x : α, F x * feature k x)) := by
                      simpa only [mul_assoc]

/-- The reflection kernel arising from a Gram certificate is symmetric. -/
theorem finite_os_reflection_kernel_symmetric
    (K : FiniteOSReflectionGramCertificate)
    (x y : K.PositiveConfiguration) :
    K.kernel x y = K.kernel y x := by
  rw [K.kernel_decomposition, K.kernel_decomposition]
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The unnormalized Osterwalder--Schrader quadratic form. -/
def FiniteOSReflectionGramCertificate.reflectionForm
    (K : FiniteOSReflectionGramCertificate)
    (F : K.PositiveConfiguration → ℝ) : ℝ :=
  ∑ x : K.PositiveConfiguration,
    ∑ y : K.PositiveConfiguration, F x * K.kernel x y * F y

/-- The OS form is the displayed weighted sum of squares, derived solely from
the pointwise Gram decomposition of the kernel. -/
theorem finite_os_reflectionForm_eq_weighted_sum_sq
    (K : FiniteOSReflectionGramCertificate)
    (F : K.PositiveConfiguration → ℝ) :
    K.reflectionForm F =
      ∑ k : K.Feature,
        K.coefficient k *
          (∑ x : K.PositiveConfiguration, F x * K.feature k x) ^ 2 := by
  unfold FiniteOSReflectionGramCertificate.reflectionForm
  simp_rw [K.kernel_decomposition]
  exact finite_gram_quadratic_identity K.coefficient K.feature F

/-- Gram factorization proves finite Osterwalder--Schrader reflection
positivity. -/
theorem finite_os_reflectionForm_nonneg
    (K : FiniteOSReflectionGramCertificate)
    (F : K.PositiveConfiguration → ℝ) :
    0 ≤ K.reflectionForm F := by
  rw [finite_os_reflectionForm_eq_weighted_sum_sq]
  exact Finset.sum_nonneg fun k _hk =>
    mul_nonneg (K.coefficient_nonneg k) (sq_nonneg _)

/-- Reflection positivity of a finite kernel, stated as a reusable predicate. -/
def FiniteOSReflectionPositive
    (K : FiniteOSReflectionGramCertificate) : Prop :=
  ∀ F : K.PositiveConfiguration → ℝ, 0 ≤ K.reflectionForm F

/-- Every nonnegative Gram certificate is reflection positive. -/
theorem finite_os_gram_certificate_reflectionPositive
    (K : FiniteOSReflectionGramCertificate) :
    FiniteOSReflectionPositive K :=
  finite_os_reflectionForm_nonneg K

/-- Wilson-specific reflection decomposition data.

`assemble x y` glues negative and positive half-lattice configurations.  The
reflection exchanges the two halves.  `kernel_eq_wilson_weight` identifies the
reflection kernel with the finite-volume Wilson Boltzmann factor.  The remaining
substantive lattice theorem is the nonnegative character expansion encoded by
`gram` and `gram_kernel_agrees`.
-/
structure FiniteLatticeWilsonOSReflectionCertificate
    (L : FiniteLatticeWilsonSystem) where
  PositiveConfiguration : Type
  [positiveFintype : Fintype PositiveConfiguration]
  [positiveInhabited : Inhabited PositiveConfiguration]
  assemble : PositiveConfiguration → PositiveConfiguration → L.Configuration
  reflection : L.Configuration → L.Configuration
  reflection_involutive : Function.Involutive reflection
  reflection_assemble :
    ∀ x y, reflection (assemble x y) = assemble y x
  kernel : PositiveConfiguration → PositiveConfiguration → ℝ
  kernel_eq_wilson_weight :
    ∀ x y,
      kernel x y =
        Real.exp (-L.beta * L.wilsonAction (assemble x y))
  gram : FiniteOSReflectionGramCertificate
  positiveConfigurationEquiv :
    PositiveConfiguration ≃ gram.PositiveConfiguration
  gram_kernel_agrees :
    ∀ x y,
      gram.kernel
        (positiveConfigurationEquiv x)
        (positiveConfigurationEquiv y) = kernel x y

attribute [instance]
  FiniteLatticeWilsonOSReflectionCertificate.positiveFintype
  FiniteLatticeWilsonOSReflectionCertificate.positiveInhabited

/-- The Wilson reflection form, expressed directly through the Boltzmann kernel. -/
def FiniteLatticeWilsonOSReflectionCertificate.wilsonReflectionForm
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (F : R.PositiveConfiguration → ℝ) : ℝ :=
  ∑ x : R.PositiveConfiguration,
    ∑ y : R.PositiveConfiguration, F x * R.kernel x y * F y

/-- A transport field exposing the equality between the Wilson reflection form
and its Gram form.  Keeping this equality explicit avoids hiding the essential
character-expansion step behind a generic readiness proposition. -/
structure FiniteLatticeWilsonOSGramBridge
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L) where
  transportObservable :
    (R.PositiveConfiguration → ℝ) →
      (R.gram.PositiveConfiguration → ℝ)
  reflectionForm_eq :
    ∀ F,
      R.wilsonReflectionForm F =
        R.gram.reflectionForm (transportObservable F)

/-- The Wilson Boltzmann kernel is reflection positive once its crossing-plane
part has the displayed nonnegative Gram/character expansion. -/
theorem finite_lattice_wilson_os_reflection_positive
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R)
    (F : R.PositiveConfiguration → ℝ) :
    0 ≤ R.wilsonReflectionForm F := by
  rw [B.reflectionForm_eq F]
  exact finite_os_reflectionForm_nonneg R.gram (B.transportObservable F)

/-- Predicate form of finite-lattice Wilson OS positivity. -/
def FiniteLatticeWilsonOSReflectionPositive
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L) : Prop :=
  ∀ F : R.PositiveConfiguration → ℝ,
    0 ≤ R.wilsonReflectionForm F

/-- A Gram bridge discharges the finite Wilson OS-positivity obligation. -/
theorem finite_lattice_wilson_os_gram_bridge_closes_reflectionPositivity
    {L : FiniteLatticeWilsonSystem}
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R) :
    FiniteLatticeWilsonOSReflectionPositive R := by
  intro F
  exact finite_lattice_wilson_os_reflection_positive R B F

/-- Normalization by a positive partition function preserves reflection
positivity. -/
def normalizedOSReflectionForm
    {α : Type} [Fintype α]
    (kernel : α → α → ℝ) (partitionFunction : ℝ)
    (F : α → ℝ) : ℝ :=
  partitionFunction⁻¹ *
    (∑ x : α, ∑ y : α, F x * kernel x y * F y)

/-- Positive normalization preserves nonnegativity of the OS form. -/
theorem normalized_os_reflectionForm_nonneg
    {α : Type} [Fintype α]
    {kernel : α → α → ℝ} {Z : ℝ}
    (hZ : 0 < Z)
    (hOS : ∀ F : α → ℝ,
      0 ≤ ∑ x : α, ∑ y : α, F x * kernel x y * F y)
    (F : α → ℝ) :
    0 ≤ normalizedOSReflectionForm kernel Z F := by
  unfold normalizedOSReflectionForm
  exact mul_nonneg (inv_nonneg.mpr hZ.le) (hOS F)

/-- Audit-visible decomposition of the finite-volume OS step.

The general positivity theorem is complete.  For the standard Wilson action,
the only model-specific input is the Gram/character decomposition of the
crossing-plaquette kernel and its identification with the reflected Boltzmann
weight. -/
structure FiniteWilsonOSReflectionPositivityCertificate
    (L : FiniteLatticeWilsonSystem) where
  reflectionData : FiniteLatticeWilsonOSReflectionCertificate L
  gramBridge : FiniteLatticeWilsonOSGramBridge reflectionData
  reflectionPositive :
    FiniteLatticeWilsonOSReflectionPositive reflectionData

/-- Build the complete finite-volume OS certificate from the reflection data and
its Gram bridge. -/
def finiteWilsonOSReflectionPositivityCertificate
    (L : FiniteLatticeWilsonSystem)
    (R : FiniteLatticeWilsonOSReflectionCertificate L)
    (B : FiniteLatticeWilsonOSGramBridge R) :
    FiniteWilsonOSReflectionPositivityCertificate L :=
  { reflectionData := R
    gramBridge := B
    reflectionPositive :=
      finite_lattice_wilson_os_gram_bridge_closes_reflectionPositivity R B }

end

end MathlibAnalytic
end MGAP4D
