import MGAP4D.MathlibAnalytic.FiniteWilsonOSPositiveConfigurationShiftKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate

variable {L : FiniteLatticeWilsonSystem}

/-- Exact kernel-level conditions under which a positive-half configuration
permutation becomes a symmetric positive contraction for the Wilson OS
seminorm.  The final field is stated directly as a comparison of Wilson
quadratic forms, so no ambient pointwise norm enters the construction. -/
structure PositiveConfigurationShiftCertificate
    (P : FiniteWilsonOSReflectionPositivityCertificate L) where
  shift : P.reflectionData.PositiveConfiguration ≃
    P.reflectionData.PositiveConfiguration
  kernel_shift_adjoint :
    ∀ x y : P.reflectionData.PositiveConfiguration,
      P.reflectionData.kernel (shift x) y =
        P.reflectionData.kernel x (shift y)
  shiftedKernel_quadratic_nonneg :
    ∀ F : P.reflectionData.PositiveConfiguration → ℝ,
      0 ≤ finiteWilsonOSShiftedKernelForm P
        (positiveConfigurationShiftedKernel P shift) F F
  shiftedObservable_quadratic_le :
    ∀ F : P.reflectionData.PositiveConfiguration → ℝ,
      P.reflectionData.wilsonOneLayerTransferForm
          (positiveConfigurationObservableShift shift F)
          (positiveConfigurationObservableShift shift F) ≤
        P.reflectionData.wilsonOneLayerTransferForm F F

namespace PositiveConfigurationShiftCertificate

/-- The translated Wilson kernel is symmetric precisely because the shift is
adjoint to itself through the original reflection kernel. -/
theorem shiftedKernel_symmetric
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate)
    (x y : P.reflectionData.PositiveConfiguration) :
    positiveConfigurationShiftedKernel P C.shift x y =
      positiveConfigurationShiftedKernel P C.shift y x := by
  calc
    positiveConfigurationShiftedKernel P C.shift x y =
        P.reflectionData.kernel x (C.shift y) :=
      C.kernel_shift_adjoint x y
    _ = P.reflectionData.kernel (C.shift y) x :=
      finite_lattice_wilson_os_reflection_kernel_symmetric
        P.reflectionData x (C.shift y)
    _ = positiveConfigurationShiftedKernel P C.shift y x :=
      rfl

/-- The concrete shifted-kernel bilinear form is symmetric. -/
theorem shiftedKernelForm_symmetric
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    finiteWilsonOSShiftedKernelForm P
        (positiveConfigurationShiftedKernel P C.shift) F G =
      finiteWilsonOSShiftedKernelForm P
        (positiveConfigurationShiftedKernel P C.shift) G F := by
  classical
  unfold finiteWilsonOSShiftedKernelForm
  calc
    (∑ x : P.reflectionData.PositiveConfiguration,
      ∑ y : P.reflectionData.PositiveConfiguration,
        F x * positiveConfigurationShiftedKernel P C.shift x y * G y) =
      ∑ y : P.reflectionData.PositiveConfiguration,
        ∑ x : P.reflectionData.PositiveConfiguration,
          F x * positiveConfigurationShiftedKernel P C.shift x y * G y := by
            rw [Finset.sum_comm]
    _ = ∑ y : P.reflectionData.PositiveConfiguration,
        ∑ x : P.reflectionData.PositiveConfiguration,
          G y * positiveConfigurationShiftedKernel P C.shift y x * F x := by
            apply Finset.sum_congr rfl
            intro y _hy
            apply Finset.sum_congr rfl
            intro x _hx
            rw [C.shiftedKernel_symmetric x y]
            ring
    _ = ∑ x : P.reflectionData.PositiveConfiguration,
        ∑ y : P.reflectionData.PositiveConfiguration,
          G x * positiveConfigurationShiftedKernel P C.shift x y * F y := by
            rfl

/-- The raw observable shift is norm nonincreasing for the OS seminorm. -/
theorem norm_positiveConfigurationShiftCarrierLinearMap_le
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate)
    (F : P.OneLayerCarrier) :
    ‖positiveConfigurationShiftCarrierLinearMap P C.shift F‖ ≤ ‖F‖ := by
  have hsq :
      ‖positiveConfigurationShiftCarrierLinearMap P C.shift F‖ ^ 2 ≤
        ‖F‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq,
      ← real_inner_self_eq_norm_sq,
      P.inner_eq_wilsonOneLayerTransferForm,
      P.inner_eq_wilsonOneLayerTransferForm]
    exact C.shiftedObservable_quadratic_le F.observable
  nlinarith [norm_nonneg
    (positiveConfigurationShiftCarrierLinearMap P C.shift F),
    norm_nonneg F]

/-- The raw shift is symmetric for the Wilson OS inner product. -/
theorem inner_positiveConfigurationShiftCarrierLinearMap_left_eq_right
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate)
    (F G : P.OneLayerCarrier) :
    inner ℝ (positiveConfigurationShiftCarrierLinearMap P C.shift F) G =
      inner ℝ F
        (positiveConfigurationShiftCarrierLinearMap P C.shift G) := by
  calc
    inner ℝ (positiveConfigurationShiftCarrierLinearMap P C.shift F) G =
        finiteWilsonOSShiftedKernelForm P
          (positiveConfigurationShiftedKernel P C.shift)
          F.observable G.observable :=
      (positiveConfigurationShiftedKernelForm_eq_inner
        P C.shift F.observable G.observable).symm
    _ = finiteWilsonOSShiftedKernelForm P
          (positiveConfigurationShiftedKernel P C.shift)
          G.observable F.observable :=
      C.shiftedKernelForm_symmetric F.observable G.observable
    _ = inner ℝ
          (positiveConfigurationShiftCarrierLinearMap P C.shift G) F :=
      positiveConfigurationShiftedKernelForm_eq_inner
        P C.shift G.observable F.observable
    _ = inner ℝ F
          (positiveConfigurationShiftCarrierLinearMap P C.shift G) :=
      real_inner_comm _ _

/-- The raw shift has nonnegative Wilson OS quadratic form. -/
theorem positiveConfigurationShiftCarrierLinearMap_quadratic_nonneg
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate)
    (F : P.OneLayerCarrier) :
    0 ≤ inner ℝ
      (positiveConfigurationShiftCarrierLinearMap P C.shift F) F := by
  rw [← positiveConfigurationShiftedKernelForm_eq_inner P C.shift]
  exact C.shiftedKernel_quadratic_nonneg F.observable

/-- Kernel-level positive-shift geometry automatically constructs the complete
raw shifted-kernel certificate used by the quotient/completion package. -/
def toOneLayerShiftedKernelCertificate
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate) :
    P.OneLayerShiftedKernelCertificate where
  shiftedKernel := positiveConfigurationShiftedKernel P C.shift
  carrierShiftLinearMap :=
    positiveConfigurationShiftCarrierLinearMap P C.shift
  shiftedKernelForm_eq_inner :=
    positiveConfigurationShiftedKernelForm_eq_inner P C.shift
  norm_carrierShiftLinearMap_le :=
    C.norm_positiveConfigurationShiftCarrierLinearMap_le
  inner_carrierShiftLinearMap_left_eq_right :=
    C.inner_positiveConfigurationShiftCarrierLinearMap_left_eq_right
  carrierShiftLinearMap_quadratic_nonneg :=
    C.positiveConfigurationShiftCarrierLinearMap_quadratic_nonneg

@[simp] theorem toOneLayerShiftedKernelCertificate_shiftedKernel
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate) :
    C.toOneLayerShiftedKernelCertificate.shiftedKernel =
      positiveConfigurationShiftedKernel P C.shift :=
  rfl

@[simp] theorem toOneLayerShiftedKernelCertificate_carrierShift_apply
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate)
    (F : P.OneLayerCarrier) :
    C.toOneLayerShiftedKernelCertificate.carrierShiftLinearMap F =
      positiveConfigurationShiftCarrierLinearMap P C.shift F :=
  rfl

/-- The identity positive-configuration shift is the canonical trivial
certificate. -/
def identity
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    P.PositiveConfigurationShiftCertificate where
  shift := Equiv.refl _
  kernel_shift_adjoint := by
    intro x y
    rfl
  shiftedKernel_quadratic_nonneg := by
    intro F
    change 0 ≤ P.reflectionData.wilsonOneLayerTransferForm F F
    exact finite_lattice_wilson_os_oneLayerTransferForm_nonneg
      P.reflectionData P.gramBridge F
  shiftedObservable_quadratic_le := by
    intro F
    exact le_rfl

@[simp] theorem identity_shift
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    (identity P).shift = Equiv.refl _ :=
  rfl

/-- Public kernel-to-certificate construction receipt. -/
theorem finiteWilsonOSPositiveConfigurationShiftCertificatePackage
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.PositiveConfigurationShiftCertificate) :
    (∀ x y : P.reflectionData.PositiveConfiguration,
      positiveConfigurationShiftedKernel P C.shift x y =
        positiveConfigurationShiftedKernel P C.shift y x) ∧
    (∀ F : P.reflectionData.PositiveConfiguration → ℝ,
      0 ≤ finiteWilsonOSShiftedKernelForm P
        (positiveConfigurationShiftedKernel P C.shift) F F) ∧
    (∀ F : P.OneLayerCarrier,
      ‖C.toOneLayerShiftedKernelCertificate.carrierShiftLinearMap F‖ ≤
        ‖F‖) := by
  exact ⟨C.shiftedKernel_symmetric,
    C.shiftedKernel_quadratic_nonneg,
    C.norm_positiveConfigurationShiftCarrierLinearMap_le⟩

end PositiveConfigurationShiftCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
