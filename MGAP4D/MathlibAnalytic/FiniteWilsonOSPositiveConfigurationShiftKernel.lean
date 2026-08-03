import MGAP4D.MathlibAnalytic.FiniteWilsonOSShiftedKernelCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate

variable {L : FiniteLatticeWilsonSystem}

/-- The concrete one-step kernel obtained by translating the positive-half
configuration in the first Wilson reflection-kernel argument. -/
def positiveConfigurationShiftedKernel
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (x y : P.reflectionData.PositiveConfiguration) : ℝ :=
  P.reflectionData.kernel (shift x) y

@[simp] theorem positiveConfigurationShiftedKernel_apply
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (x y : P.reflectionData.PositiveConfiguration) :
    positiveConfigurationShiftedKernel P shift x y =
      P.reflectionData.kernel (shift x) y :=
  rfl

/-- Pullback of positive-half observables by the inverse configuration shift.
This is the raw observable action whose Wilson matrix elements are represented
by `positiveConfigurationShiftedKernel`. -/
def positiveConfigurationObservableShift
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (F : P.reflectionData.PositiveConfiguration → ℝ) :
    P.reflectionData.PositiveConfiguration → ℝ :=
  fun x => F (shift.symm x)

@[simp] theorem positiveConfigurationObservableShift_apply
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (F : P.reflectionData.PositiveConfiguration → ℝ)
    (x : P.reflectionData.PositiveConfiguration) :
    positiveConfigurationObservableShift shift F x = F (shift.symm x) :=
  rfl

/-- The positive-half configuration shift as a real-linear endomorphism of the
raw Wilson OS carrier. -/
def positiveConfigurationShiftCarrierLinearMap
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration) :
    P.OneLayerCarrier →ₗ[ℝ] P.OneLayerCarrier where
  toFun := fun F =>
    ⟨positiveConfigurationObservableShift shift F.observable⟩
  map_add' := by
    intro F G
    apply P.OneLayerCarrier.observable_injective
    rfl
  map_smul' := by
    intro r F
    apply P.OneLayerCarrier.observable_injective
    rfl

@[simp] theorem positiveConfigurationShiftCarrierLinearMap_observable
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (F : P.OneLayerCarrier) :
    (positiveConfigurationShiftCarrierLinearMap P shift F).observable =
      positiveConfigurationObservableShift shift F.observable :=
  rfl

/-- Reindexing the finite positive-half sum identifies the concrete shifted
Wilson kernel with the matrix elements of the observable pullback. -/
theorem positiveConfigurationShiftedKernelForm_eq_inner
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    finiteWilsonOSShiftedKernelForm P
        (positiveConfigurationShiftedKernel P shift) F G =
      inner ℝ
        (positiveConfigurationShiftCarrierLinearMap P shift ⟨F⟩)
        (⟨G⟩ : P.OneLayerCarrier) := by
  classical
  rw [P.inner_eq_wilsonOneLayerTransferForm]
  change
    (∑ x : P.reflectionData.PositiveConfiguration,
      ∑ y : P.reflectionData.PositiveConfiguration,
        F x * P.reflectionData.kernel (shift x) y * G y) =
      ∑ x : P.reflectionData.PositiveConfiguration,
        ∑ y : P.reflectionData.PositiveConfiguration,
          F (shift.symm x) * P.reflectionData.kernel x y * G y
  refine Fintype.sum_equiv shift _ _ ?_
  intro x
  simp only [Equiv.symm_apply_apply]

/-- Point-mass observable at a positive-half configuration. -/
def positiveConfigurationPointObservable
    {P : FiniteWilsonOSReflectionPositivityCertificate L}
    (x : P.reflectionData.PositiveConfiguration) :
    P.reflectionData.PositiveConfiguration → ℝ :=
  fun z => if z = x then 1 else 0

/-- Point-mass observables recover an arbitrary shifted-kernel entry exactly. -/
theorem positiveConfigurationShiftedKernelForm_pointObservable
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (x y : P.reflectionData.PositiveConfiguration) :
    finiteWilsonOSShiftedKernelForm P
        (positiveConfigurationShiftedKernel P shift)
        (positiveConfigurationPointObservable x)
        (positiveConfigurationPointObservable y) =
      positiveConfigurationShiftedKernel P shift x y := by
  classical
  simp [finiteWilsonOSShiftedKernelForm,
    positiveConfigurationPointObservable,
    positiveConfigurationShiftedKernel]

/-- Point-mass observables also recover the original unshifted Wilson kernel. -/
theorem wilsonOneLayerTransferForm_pointObservable
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (x y : P.reflectionData.PositiveConfiguration) :
    P.reflectionData.wilsonOneLayerTransferForm
        (positiveConfigurationPointObservable x)
        (positiveConfigurationPointObservable y) =
      P.reflectionData.kernel x y := by
  classical
  simp [FiniteLatticeWilsonOSReflectionCertificate.wilsonOneLayerTransferForm,
    positiveConfigurationPointObservable]

/-- The shifted kernel is the actual finite Wilson Boltzmann weight of the
assembled configuration with the first half translated. -/
theorem positiveConfigurationShiftedKernel_eq_wilsonWeight
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (x y : P.reflectionData.PositiveConfiguration) :
    positiveConfigurationShiftedKernel P shift x y =
      Real.exp
        (-L.beta *
          L.wilsonAction (P.reflectionData.assemble (shift x) y)) := by
  exact P.reflectionData.kernel_eq_wilson_weight (shift x) y

/-- At nonzero coupling, a genuine Wilson-action change produces a pointwise
shifted-kernel difference from the unshifted reflection kernel. -/
theorem positiveConfigurationShiftedKernel_ne_unshifted_of_wilsonAction_ne
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (x y : P.reflectionData.PositiveConfiguration)
    (hBeta : L.beta ≠ 0)
    (hAction :
      L.wilsonAction (P.reflectionData.assemble (shift x) y) ≠
        L.wilsonAction (P.reflectionData.assemble x y)) :
    positiveConfigurationShiftedKernel P shift x y ≠
      P.reflectionData.kernel x y := by
  rw [positiveConfigurationShiftedKernel_eq_wilsonWeight,
    P.reflectionData.kernel_eq_wilson_weight]
  intro h
  apply hAction
  have hExponent :
      -L.beta *
          L.wilsonAction (P.reflectionData.assemble (shift x) y) =
        -L.beta * L.wilsonAction (P.reflectionData.assemble x y) :=
    Real.exp_injective h
  exact mul_left_cancel₀ (neg_ne_zero.mpr hBeta) hExponent

/-- A pointwise kernel difference yields an explicit observable-pair difference
between the shifted form and the original Wilson reflection form. -/
theorem exists_shiftedKernelForm_ne_unshifted_of_kernel_ne
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (shift : P.reflectionData.PositiveConfiguration ≃
      P.reflectionData.PositiveConfiguration)
    (x y : P.reflectionData.PositiveConfiguration)
    (hKernel : positiveConfigurationShiftedKernel P shift x y ≠
      P.reflectionData.kernel x y) :
    ∃ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSShiftedKernelForm P
          (positiveConfigurationShiftedKernel P shift) F G ≠
        P.reflectionData.wilsonOneLayerTransferForm F G := by
  refine ⟨positiveConfigurationPointObservable x,
    positiveConfigurationPointObservable y, ?_⟩
  rw [positiveConfigurationShiftedKernelForm_pointObservable,
    wilsonOneLayerTransferForm_pointObservable]
  exact hKernel

end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
