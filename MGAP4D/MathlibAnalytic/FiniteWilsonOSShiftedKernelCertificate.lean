import MGAP4D.MathlibAnalytic.FiniteWilsonOSOneLayerHilbertCompletion
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate

variable {L : FiniteLatticeWilsonSystem}

/-- Bilinear form carried by an independent shifted geometric kernel on the
positive-half configuration space.  This is separate from the unshifted
reflection kernel used to define the OS Hilbert inner product. -/
def finiteWilsonOSShiftedKernelForm
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shiftedKernel :
      P.reflectionData.PositiveConfiguration →
        P.reflectionData.PositiveConfiguration → ℝ)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) : ℝ :=
  ∑ x : P.reflectionData.PositiveConfiguration,
    ∑ y : P.reflectionData.PositiveConfiguration,
      F x * shiftedKernel x y * G y

/-- Exact data required to turn an independent shifted geometric Wilson kernel
into a contractive symmetric positive shift on the raw OS seminormed carrier.
The kernel-to-carrier matrix identity is explicit; no temporal interpretation is
inferred from the unshifted reflection form. -/
structure OneLayerShiftedKernelCertificate
    (P : FiniteWilsonOSReflectionPositivityCertificate L) where
  shiftedKernel :
    P.reflectionData.PositiveConfiguration →
      P.reflectionData.PositiveConfiguration → ℝ
  carrierShiftLinearMap : P.OneLayerCarrier →ₗ[ℝ] P.OneLayerCarrier
  shiftedKernelForm_eq_inner :
    ∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P shiftedKernel F G =
        inner ℝ (carrierShiftLinearMap ⟨F⟩) ⟨G⟩
  norm_carrierShiftLinearMap_le :
    ∀ F : P.OneLayerCarrier,
      ‖carrierShiftLinearMap F‖ ≤ ‖F‖
  inner_carrierShiftLinearMap_left_eq_right :
    ∀ F G : P.OneLayerCarrier,
      inner ℝ (carrierShiftLinearMap F) G =
        inner ℝ F (carrierShiftLinearMap G)
  carrierShiftLinearMap_quadratic_nonneg :
    ∀ F : P.OneLayerCarrier,
      0 ≤ inner ℝ (carrierShiftLinearMap F) F

namespace OneLayerShiftedKernelCertificate

/-- The shifted kernel form is symmetric because its carrier realization is
symmetric for the OS inner product. -/
theorem shiftedKernelForm_symmetric
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G =
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel G F := by
  calc
    finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G =
        inner ℝ (C.carrierShiftLinearMap ⟨F⟩) ⟨G⟩ :=
      C.shiftedKernelForm_eq_inner F G
    _ = inner ℝ (⟨F⟩ : P.OneLayerCarrier)
        (C.carrierShiftLinearMap ⟨G⟩) :=
      C.inner_carrierShiftLinearMap_left_eq_right ⟨F⟩ ⟨G⟩
    _ = inner ℝ (C.carrierShiftLinearMap ⟨G⟩)
        (⟨F⟩ : P.OneLayerCarrier) := real_inner_comm _ _
    _ = finiteWilsonOSShiftedKernelForm P C.shiftedKernel G F :=
      (C.shiftedKernelForm_eq_inner G F).symm

/-- The shifted kernel form is nonnegative on the diagonal. -/
theorem shiftedKernelForm_nonneg
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.reflectionData.PositiveConfiguration → ℝ) :
    0 ≤ finiteWilsonOSShiftedKernelForm P C.shiftedKernel F F := by
  rw [C.shiftedKernelForm_eq_inner]
  exact C.carrierShiftLinearMap_quadratic_nonneg ⟨F⟩

/-- Contractivity forces preservation of the exact OS-null submodule. -/
theorem carrierShiftLinearMap_mem_oneLayerNullSubmodule
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.OneLayerCarrier)
    (hF : F ∈ P.oneLayerNullSubmodule) :
    C.carrierShiftLinearMap F ∈ P.oneLayerNullSubmodule := by
  rw [P.mem_oneLayerNullSubmodule] at hF ⊢
  apply le_antisymm
  · calc
      ‖C.carrierShiftLinearMap F‖ ≤ ‖F‖ :=
        C.norm_carrierShiftLinearMap_le F
      _ = 0 := hF
  · exact norm_nonneg _

/-- The raw carrier shift bundled as a continuous linear contraction. -/
noncomputable def carrierShiftContinuousLinearMap
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate) :
    P.OneLayerCarrier →L[ℝ] P.OneLayerCarrier :=
  C.carrierShiftLinearMap.mkContinuous 1 (by
    intro F
    simpa using C.norm_carrierShiftLinearMap_le F)

@[simp] theorem carrierShiftContinuousLinearMap_apply
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.OneLayerCarrier) :
    C.carrierShiftContinuousLinearMap F = C.carrierShiftLinearMap F :=
  rfl

/-- The continuous carrier shift remains norm nonincreasing. -/
theorem norm_carrierShiftContinuousLinearMap_le
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.OneLayerCarrier) :
    ‖C.carrierShiftContinuousLinearMap F‖ ≤ ‖F‖ :=
  C.norm_carrierShiftLinearMap_le F

/-- The unshifted reflection kernel gives the canonical identity shifted-kernel
certificate.  This baseline is mathematically trivial and is used only to
separate genuine shifted data from the original OS inner product. -/
noncomputable def identity
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    P.OneLayerShiftedKernelCertificate where
  shiftedKernel := P.reflectionData.kernel
  carrierShiftLinearMap := LinearMap.id
  shiftedKernelForm_eq_inner := by
    intro F G
    change
      P.reflectionData.wilsonOneLayerTransferForm F G =
        inner ℝ (⟨F⟩ : P.OneLayerCarrier) ⟨G⟩
    rw [P.inner_eq_wilsonOneLayerTransferForm]
  norm_carrierShiftLinearMap_le := by
    intro F
    exact le_rfl
  inner_carrierShiftLinearMap_left_eq_right := by
    intro F G
    rfl
  carrierShiftLinearMap_quadratic_nonneg := by
    intro F
    exact real_inner_self_nonneg

@[simp] theorem identity_shiftedKernel
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    (identity P).shiftedKernel = P.reflectionData.kernel :=
  rfl

@[simp] theorem identity_carrierShiftLinearMap_apply
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (F : P.OneLayerCarrier) :
    (identity P).carrierShiftLinearMap F = F :=
  rfl

/-- Public raw shifted-kernel receipt. -/
theorem finiteWilsonOSShiftedKernelCertificatePackage
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (C : P.OneLayerShiftedKernelCertificate) :
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G =
        finiteWilsonOSShiftedKernelForm P C.shiftedKernel G F) ∧
    (∀ F : P.reflectionData.PositiveConfiguration → ℝ,
      0 ≤ finiteWilsonOSShiftedKernelForm P C.shiftedKernel F F) ∧
    (∀ F : P.OneLayerCarrier,
      ‖C.carrierShiftContinuousLinearMap F‖ ≤ ‖F‖) := by
  exact ⟨C.shiftedKernelForm_symmetric,
    C.shiftedKernelForm_nonneg,
    C.norm_carrierShiftContinuousLinearMap_le⟩

end OneLayerShiftedKernelCertificate

end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
