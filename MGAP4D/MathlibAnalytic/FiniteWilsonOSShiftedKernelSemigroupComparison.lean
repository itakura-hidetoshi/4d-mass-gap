import MGAP4D.MathlibAnalytic.FiniteWilsonOSShiftedKernelHilbertOperator
import MGAP4D.MathlibAnalytic.FiniteWilsonOSOneLayerIdentityTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate
namespace OneLayerShiftedKernelCertificate

variable {L : FiniteLatticeWilsonSystem}
  {P : FiniteWilsonOSReflectionPositivityCertificate L}

/-- Natural iterates of the raw carrier shift. -/
def carrierShiftIterate
    (C : P.OneLayerShiftedKernelCertificate) :
    ℕ → P.OneLayerCarrier →ₗ[ℝ] P.OneLayerCarrier
  | 0 => LinearMap.id
  | n + 1 => C.carrierShiftLinearMap.comp (C.carrierShiftIterate n)

@[simp] theorem carrierShiftIterate_zero
    (C : P.OneLayerShiftedKernelCertificate) :
    C.carrierShiftIterate 0 = LinearMap.id :=
  rfl

@[simp] theorem carrierShiftIterate_succ_apply
    (C : P.OneLayerShiftedKernelCertificate)
    (n : ℕ) (F : P.OneLayerCarrier) :
    C.carrierShiftIterate (n + 1) F =
      C.carrierShiftLinearMap (C.carrierShiftIterate n F) :=
  rfl

/-- The completed discrete shifted geometric OS semigroup. -/
def hilbertShiftSemigroup
    (C : P.OneLayerShiftedKernelCertificate) :
    ℕ → P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert
  | 0 => 1
  | n + 1 =>
      C.hilbertShiftContinuousLinearMap.comp (C.hilbertShiftSemigroup n)

@[simp] theorem hilbertShiftSemigroup_zero
    (C : P.OneLayerShiftedKernelCertificate) :
    C.hilbertShiftSemigroup 0 = 1 :=
  rfl

@[simp] theorem hilbertShiftSemigroup_succ_apply
    (C : P.OneLayerShiftedKernelCertificate)
    (n : ℕ) (x : P.OneLayerHilbert) :
    C.hilbertShiftSemigroup (n + 1) x =
      C.hilbertShiftContinuousLinearMap (C.hilbertShiftSemigroup n x) :=
  rfl

/-- The natural-time family satisfies the additive semigroup law pointwise. -/
theorem hilbertShiftSemigroup_add_apply
    (C : P.OneLayerShiftedKernelCertificate)
    (m n : ℕ) (x : P.OneLayerHilbert) :
    C.hilbertShiftSemigroup (m + n) x =
      C.hilbertShiftSemigroup m (C.hilbertShiftSemigroup n x) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [Nat.succ_add, hilbertShiftSemigroup_succ_apply]
      rw [ih]

/-- Bundled additive semigroup law. -/
theorem hilbertShiftSemigroup_add
    (C : P.OneLayerShiftedKernelCertificate)
    (m n : ℕ) :
    C.hilbertShiftSemigroup (m + n) =
      (C.hilbertShiftSemigroup m).comp (C.hilbertShiftSemigroup n) := by
  apply ContinuousLinearMap.ext
  intro x
  exact C.hilbertShiftSemigroup_add_apply m n x

/-- Every discrete shifted geometric time is contractive. -/
theorem norm_hilbertShiftSemigroup_le
    (C : P.OneLayerShiftedKernelCertificate)
    (n : ℕ) (x : P.OneLayerHilbert) :
    ‖C.hilbertShiftSemigroup n x‖ ≤ ‖x‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        ‖C.hilbertShiftSemigroup (n + 1) x‖ =
            ‖C.hilbertShiftContinuousLinearMap
              (C.hilbertShiftSemigroup n x)‖ := rfl
        _ ≤ ‖C.hilbertShiftSemigroup n x‖ :=
          C.norm_hilbertShiftContinuousLinearMap_le _
        _ ≤ ‖x‖ := ih

/-- The completed semigroup acts on represented states by the corresponding raw
carrier iterate. -/
theorem hilbertShiftSemigroup_oneLayerState
    (C : P.OneLayerShiftedKernelCertificate)
    (n : ℕ) (F : P.OneLayerCarrier) :
    C.hilbertShiftSemigroup n (P.oneLayerState F) =
      P.oneLayerState (C.carrierShiftIterate n F) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [C.hilbertShiftSemigroup_succ_apply, ih,
        C.hilbertShiftContinuousLinearMap_oneLayerState]
      rfl

/-- Iterated shifted geometric matrix elements on the dense observable image. -/
theorem hilbertShiftSemigroup_matrixElement
    (C : P.OneLayerShiftedKernelCertificate)
    (n : ℕ)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    inner ℝ
        (C.hilbertShiftSemigroup n (P.oneLayerObservableEmbedding F))
        (P.oneLayerObservableEmbedding G) =
      inner ℝ (C.carrierShiftIterate n ⟨F⟩)
        (⟨G⟩ : P.OneLayerCarrier) := by
  rw [P.oneLayerObservableEmbedding_apply,
    P.oneLayerObservableEmbedding_apply,
    C.hilbertShiftSemigroup_oneLayerState,
    P.inner_oneLayerState_oneLayerState]

/-- Defect between the shifted geometric kernel operator and the original
unshifted Wilson reflection form. -/
noncomputable def unshiftedReflectionMatrixDefect
    (C : P.OneLayerShiftedKernelCertificate)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) : ℝ :=
  finiteWilsonOSOneLayerOperatorMatrixDefect
    P.reflectionData P.oneLayerObservableEmbedding
      C.hilbertShiftContinuousLinearMap F G

/-- The reflection defect is exactly original form minus shifted-kernel form. -/
theorem unshiftedReflectionMatrixDefect_eq_sub
    (C : P.OneLayerShiftedKernelCertificate)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    C.unshiftedReflectionMatrixDefect F G =
      P.reflectionData.wilsonOneLayerTransferForm F G -
        finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G := by
  unfold unshiftedReflectionMatrixDefect
    finiteWilsonOSOneLayerOperatorMatrixDefect
  rw [C.hilbertShiftContinuousLinearMap_matrixElement]

/-- All reflection defects vanish exactly when the shifted completed operator is
the identity transfer. -/
theorem all_unshiftedReflectionMatrixDefects_eq_zero_iff
    (C : P.OneLayerShiftedKernelCertificate) :
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      C.unshiftedReflectionMatrixDefect F G = 0) ↔
      C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer := by
  exact P.oneLayerOperator_all_matrixDefects_eq_zero_iff
    C.hilbertShiftContinuousLinearMap

/-- Equality of the independent shifted kernel form with the original
reflection form is equivalent to triviality of the completed shifted operator. -/
theorem shiftedKernelForm_eq_unshiftedReflectionForm_iff
    (C : P.OneLayerShiftedKernelCertificate) :
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G =
        P.reflectionData.wilsonOneLayerTransferForm F G) ↔
      C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer := by
  rw [← C.all_unshiftedReflectionMatrixDefects_eq_zero_iff]
  constructor
  · intro h F G
    rw [C.unshiftedReflectionMatrixDefect_eq_sub, h F G, sub_self]
  · intro h F G
    have hD := h F G
    rw [C.unshiftedReflectionMatrixDefect_eq_sub, sub_eq_zero] at hD
    exact hD.symm

/-- A nonidentity shifted operator has an explicit kernel-form witness that
separates it from the unshifted reflection form. -/
theorem exists_shiftedKernelForm_ne_unshifted_of_operator_ne_identity
    (C : P.OneLayerShiftedKernelCertificate)
    (hC : C.hilbertShiftContinuousLinearMap ≠ P.oneLayerIdentityTransfer) :
    ∃ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G ≠
        P.reflectionData.wilsonOneLayerTransferForm F G := by
  by_contra h
  push_neg at h
  apply hC
  exact (C.shiftedKernelForm_eq_unshiftedReflectionForm_iff).mp h

/-- The identity shifted-kernel certificate completes to the canonical identity
transfer. -/
@[simp] theorem identity_hilbertShiftContinuousLinearMap
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    (identity P).hilbertShiftContinuousLinearMap =
      P.oneLayerIdentityTransfer := by
  apply
    ((identity P).shiftedKernelForm_eq_unshiftedReflectionForm_iff).mp
  intro F G
  rfl

/-- Public semigroup and reflection-comparison receipt. -/
theorem finiteWilsonOSShiftedKernelSemigroupComparisonPackage
    (C : P.OneLayerShiftedKernelCertificate) :
    (∀ m n : ℕ,
      C.hilbertShiftSemigroup (m + n) =
        (C.hilbertShiftSemigroup m).comp
          (C.hilbertShiftSemigroup n)) ∧
    (∀ n : ℕ, ∀ x : P.OneLayerHilbert,
      ‖C.hilbertShiftSemigroup n x‖ ≤ ‖x‖) ∧
    ((∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G =
        P.reflectionData.wilsonOneLayerTransferForm F G) ↔
      C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer) := by
  exact ⟨C.hilbertShiftSemigroup_add,
    C.norm_hilbertShiftSemigroup_le,
    C.shiftedKernelForm_eq_unshiftedReflectionForm_iff⟩

end OneLayerShiftedKernelCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
