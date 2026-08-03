import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPositiveShiftKernelPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate
namespace PositiveConfigurationShiftCertificate

variable {L : FiniteLatticeWilsonSystem}
  {P : FiniteWilsonOSReflectionPositivityCertificate L}

/-- Terminal package for a positive-half configuration shift.  It combines the
kernel construction, quotient/completion operator, natural-time semigroup,
Boltzmann formula, and the exact nontriviality criterion at nonzero coupling. -/
theorem physicalYangMillsGaugeInvariantFiniteWilsonPositiveShiftKernelFinalPackage
    (C : P.PositiveConfigurationShiftCertificate) :
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P
          (positiveConfigurationShiftedKernel P C.shift) F G =
        inner ℝ
          (C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap
            (P.oneLayerObservableEmbedding F))
          (P.oneLayerObservableEmbedding G)) ∧
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
      ‖C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup n z‖ ≤ ‖z‖) ∧
    ((∃ x y : P.reflectionData.PositiveConfiguration,
        L.beta ≠ 0 ∧
        L.wilsonAction (P.reflectionData.assemble (C.shift x) y) ≠
          L.wilsonAction (P.reflectionData.assemble x y)) →
      C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap ≠
        P.oneLayerIdentityTransfer) := by
  refine ⟨?_,
    C.hilbertShiftSemigroup_matrixElement_eq_iteratedShiftedKernelForm,
    C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup_add,
    C.toOneLayerShiftedKernelCertificate.norm_hilbertShiftSemigroup_le,
    ?_⟩
  · intro F G
    exact
      (C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap_matrixElement
        F G).symm
  · rintro ⟨x, y, hBeta, hAction⟩
    exact C.hilbertShiftContinuousLinearMap_ne_identity_of_wilsonAction_ne
      x y hBeta hAction

/-- Exact terminal dichotomy: either every shifted Wilson matrix element agrees
with the unshifted reflection form, forcing identity, or a concrete
point-observable pair witnesses a nontrivial geometric shift. -/
theorem positiveShift_identity_or_pointObservable_witness
    (C : P.PositiveConfigurationShiftCertificate) :
    C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap =
        P.oneLayerIdentityTransfer ∨
      ∃ x y : P.reflectionData.PositiveConfiguration,
        finiteWilsonOSShiftedKernelForm P
            (positiveConfigurationShiftedKernel P C.shift)
            (positiveConfigurationPointObservable x)
            (positiveConfigurationPointObservable y) ≠
          P.reflectionData.wilsonOneLayerTransferForm
            (positiveConfigurationPointObservable x)
            (positiveConfigurationPointObservable y) := by
  classical
  by_cases hIdentity :
      C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap =
        P.oneLayerIdentityTransfer
  · exact Or.inl hIdentity
  · right
    by_contra hPoint
    push Not at hPoint
    apply hIdentity
    apply
      (C.toOneLayerShiftedKernelCertificate.shiftedKernelForm_eq_unshiftedReflectionForm_iff).mp
    intro F G
    unfold finiteWilsonOSShiftedKernelForm
      FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm
    apply Finset.sum_congr rfl
    intro x _hx
    apply Finset.sum_congr rfl
    intro y _hy
    have hxy := hPoint x y
    rw [positiveConfigurationShiftedKernelForm_pointObservable,
      wilsonOneLayerTransferForm_pointObservable] at hxy
    have hxy' :
        C.toOneLayerShiftedKernelCertificate.shiftedKernel x y =
          P.reflectionData.kernel x y := by
      simpa only [toOneLayerShiftedKernelCertificate_shiftedKernel] using hxy
    rw [hxy']

end PositiveConfigurationShiftCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
