import MGAP4D.MathlibAnalytic.FiniteWilsonOSPositiveConfigurationShiftCertificate
import MGAP4D.MathlibAnalytic.FiniteWilsonOSShiftedKernelSemigroupComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate
namespace PositiveConfigurationShiftCertificate

variable {L : FiniteLatticeWilsonSystem}
  {P : FiniteWilsonOSReflectionPositivityCertificate L}

/-- Natural iterates of the positive-half configuration permutation. -/
def shiftIterate
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ) : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration :=
  C.shift ^ n

@[simp] theorem shiftIterate_zero
    (C : P.PositiveConfigurationShiftCertificate) :
    C.shiftIterate 0 = Equiv.refl _ := by
  ext x
  rfl

@[simp] theorem shiftIterate_succ_apply
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ) (x : P.reflectionData.PositiveConfiguration) :
    C.shiftIterate (n + 1) x = C.shift (C.shiftIterate n x) := by
  change (C.shift ^ (n + 1)) x = C.shift ((C.shift ^ n) x)
  rw [pow_succ']
  rfl

/-- The actual natural-time Wilson kernel obtained by iterating the positive
configuration translation. -/
def iteratedShiftedKernel
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ)
    (x y : P.reflectionData.PositiveConfiguration) : ℝ :=
  P.reflectionData.kernel (C.shiftIterate n x) y

@[simp] theorem iteratedShiftedKernel_zero
    (C : P.PositiveConfigurationShiftCertificate)
    (x y : P.reflectionData.PositiveConfiguration) :
    C.iteratedShiftedKernel 0 x y = P.reflectionData.kernel x y := by
  simp [iteratedShiftedKernel]

@[simp] theorem iteratedShiftedKernel_succ
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ)
    (x y : P.reflectionData.PositiveConfiguration) :
    C.iteratedShiftedKernel (n + 1) x y =
      P.reflectionData.kernel (C.shift (C.shiftIterate n x)) y := by
  simp [iteratedShiftedKernel]

/-- Iterating the raw carrier map is exactly pullback by the inverse of the
iterated positive-configuration shift. -/
theorem carrierShiftIterate_observable
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ) (F : P.OneLayerCarrier) :
    (C.toOneLayerShiftedKernelCertificate.carrierShiftIterate n F).observable =
      positiveConfigurationObservableShift (C.shiftIterate n) F.observable := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp only [FiniteWilsonOSReflectionPositivityCertificate.OneLayerShiftedKernelCertificate.carrierShiftIterate_succ_apply]
      change
        positiveConfigurationObservableShift C.shift
            (C.toOneLayerShiftedKernelCertificate.carrierShiftIterate n F).observable =
          positiveConfigurationObservableShift (C.shiftIterate (n + 1))
            F.observable
      rw [ih]
      funext x
      simp [positiveConfigurationObservableShift, shiftIterate, pow_succ']

/-- The completed natural-time semigroup has exact matrix elements given by the
iterated concrete Wilson kernel. -/
theorem hilbertShiftSemigroup_matrixElement_eq_iteratedShiftedKernelForm
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    inner ℝ
        (C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup n
          (P.oneLayerObservableEmbedding F))
        (P.oneLayerObservableEmbedding G) =
      finiteWilsonOSShiftedKernelForm P
        (C.iteratedShiftedKernel n) F G := by
  rw [C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup_matrixElement]
  calc
    inner ℝ
        (C.toOneLayerShiftedKernelCertificate.carrierShiftIterate n
          (⟨F⟩ : P.OneLayerCarrier))
        (⟨G⟩ : P.OneLayerCarrier) =
      P.reflectionData.wilsonOneLayerTransferForm
        (C.toOneLayerShiftedKernelCertificate.carrierShiftIterate n
          (⟨F⟩ : P.OneLayerCarrier)).observable G :=
        P.inner_eq_wilsonOneLayerTransferForm _ _
    _ = P.reflectionData.wilsonOneLayerTransferForm
        (positiveConfigurationObservableShift (C.shiftIterate n) F) G := by
          rw [C.carrierShiftIterate_observable]
    _ = finiteWilsonOSShiftedKernelForm P
        (C.iteratedShiftedKernel n) F G := by
      have h := positiveConfigurationShiftedKernelForm_eq_inner
        P (C.shiftIterate n) F G
      rw [P.inner_eq_wilsonOneLayerTransferForm] at h
      exact h.symm

/-- Every iterated concrete kernel is the Wilson Boltzmann weight of the
assembled configuration whose first half has been translated `n` times. -/
theorem iteratedShiftedKernel_eq_wilsonWeight
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ)
    (x y : P.reflectionData.PositiveConfiguration) :
    C.iteratedShiftedKernel n x y =
      Real.exp
        (-L.beta *
          L.wilsonAction
            (P.reflectionData.assemble (C.shiftIterate n x) y)) := by
  exact P.reflectionData.kernel_eq_wilson_weight
    (C.shiftIterate n x) y

/-- A nonzero-coupling action witness at any natural time produces a concrete
observable-pair witness separating the completed semigroup from the identity
reflection form. -/
theorem exists_iteratedShiftedKernelForm_ne_unshifted_of_wilsonAction_ne
    (C : P.PositiveConfigurationShiftCertificate)
    (n : ℕ)
    (x y : P.reflectionData.PositiveConfiguration)
    (hBeta : L.beta ≠ 0)
    (hAction :
      L.wilsonAction
          (P.reflectionData.assemble (C.shiftIterate n x) y) ≠
        L.wilsonAction (P.reflectionData.assemble x y)) :
    ∃ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P (C.iteratedShiftedKernel n) F G ≠
        P.reflectionData.wilsonOneLayerTransferForm F G := by
  have hKernel :
      C.iteratedShiftedKernel n x y ≠ P.reflectionData.kernel x y := by
    rw [C.iteratedShiftedKernel_eq_wilsonWeight,
      P.reflectionData.kernel_eq_wilson_weight]
    intro h
    apply hAction
    have hExponent :
        -L.beta *
            L.wilsonAction
              (P.reflectionData.assemble (C.shiftIterate n x) y) =
          -L.beta * L.wilsonAction (P.reflectionData.assemble x y) :=
      Real.exp_injective h
    exact mul_left_cancel₀ (neg_ne_zero.mpr hBeta) hExponent
  refine ⟨positiveConfigurationPointObservable x,
    positiveConfigurationPointObservable y, ?_⟩
  classical
  simp [finiteWilsonOSShiftedKernelForm,
    positiveConfigurationPointObservable,
    iteratedShiftedKernel,
    FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm]
  exact hKernel

/-- At one step, a nonzero-coupling action witness forces the completed shifted
operator itself to be nonidentity. -/
theorem hilbertShiftContinuousLinearMap_ne_identity_of_wilsonAction_ne
    (C : P.PositiveConfigurationShiftCertificate)
    (x y : P.reflectionData.PositiveConfiguration)
    (hBeta : L.beta ≠ 0)
    (hAction :
      L.wilsonAction (P.reflectionData.assemble (C.shift x) y) ≠
        L.wilsonAction (P.reflectionData.assemble x y)) :
    C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap ≠
      P.oneLayerIdentityTransfer := by
  intro hIdentity
  have hForms :=
    (C.toOneLayerShiftedKernelCertificate.shiftedKernelForm_eq_unshiftedReflectionForm_iff).2
      hIdentity
  have hKernel :=
    positiveConfigurationShiftedKernel_ne_unshifted_of_wilsonAction_ne
      P C.shift x y hBeta hAction
  apply hKernel
  have hPoint := hForms
    (positiveConfigurationPointObservable x)
    (positiveConfigurationPointObservable y)
  have hPoint' :
      finiteWilsonOSShiftedKernelForm P
          (positiveConfigurationShiftedKernel P C.shift)
          (positiveConfigurationPointObservable x)
          (positiveConfigurationPointObservable y) =
        P.reflectionData.wilsonOneLayerTransferForm
          (positiveConfigurationPointObservable x)
          (positiveConfigurationPointObservable y) := by
    simpa only [toOneLayerShiftedKernelCertificate_shiftedKernel] using hPoint
  rw [positiveConfigurationShiftedKernelForm_pointObservable,
    wilsonOneLayerTransferForm_pointObservable] at hPoint'
  exact hPoint'

/-- Public natural-time configuration-shift semigroup receipt. -/
theorem finiteWilsonOSPositiveConfigurationShiftSemigroupPackage
    (C : P.PositiveConfigurationShiftCertificate) :
    (∀ n : ℕ, ∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      inner ℝ
          (C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup n
            (P.oneLayerObservableEmbedding F))
          (P.oneLayerObservableEmbedding G) =
        finiteWilsonOSShiftedKernelForm P
          (C.iteratedShiftedKernel n) F G) ∧
    (∀ m n : ℕ,
      C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup (m + n) =
        (C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup m).comp
          (C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup n)) ∧
    (∀ n : ℕ, ∀ z : P.OneLayerHilbert,
      ‖C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup n z‖ ≤
        ‖z‖) := by
  exact ⟨C.hilbertShiftSemigroup_matrixElement_eq_iteratedShiftedKernelForm,
    C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup_add,
    C.toOneLayerShiftedKernelCertificate.norm_hilbertShiftSemigroup_le⟩

end PositiveConfigurationShiftCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
