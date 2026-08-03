import MGAP4D.MathlibAnalytic.FiniteWilsonOSShiftedKernelCertificate
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate
namespace OneLayerShiftedKernelCertificate

variable {L : FiniteLatticeWilsonSystem}
  {P : FiniteWilsonOSReflectionPositivityCertificate L}

/-- The shifted carrier map descended functorially to the separated OS
quotient.  Uniform continuity follows from the carrier contraction. -/
noncomputable def separatedShift
    (C : P.OneLayerShiftedKernelCertificate) :
    P.OneLayerSeparated → P.OneLayerSeparated :=
  SeparationQuotient.map C.carrierShiftContinuousLinearMap

@[simp] theorem separatedShift_oneLayerClass
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.OneLayerCarrier) :
    C.separatedShift (P.oneLayerClass F) =
      P.oneLayerClass (C.carrierShiftLinearMap F) := by
  exact SeparationQuotient.map_mk
    C.carrierShiftContinuousLinearMap.uniformContinuous F

/-- The descended shifted-kernel action is real linear. -/
noncomputable def separatedShiftLinearMap
    (C : P.OneLayerShiftedKernelCertificate) :
    P.OneLayerSeparated →ₗ[ℝ] P.OneLayerSeparated where
  toFun := C.separatedShift
  map_add' := by
    intro x y
    refine Quotient.inductionOn x ?_
    intro F
    refine Quotient.inductionOn y ?_
    intro G
    change C.separatedShift (P.oneLayerClass (F + G)) =
      C.separatedShift (P.oneLayerClass F) +
        C.separatedShift (P.oneLayerClass G)
    rw [C.separatedShift_oneLayerClass,
      C.separatedShift_oneLayerClass,
      C.separatedShift_oneLayerClass, map_add]
    change SeparationQuotient.mk
        (C.carrierShiftLinearMap F + C.carrierShiftLinearMap G) =
      SeparationQuotient.mk (C.carrierShiftLinearMap F) +
        SeparationQuotient.mk (C.carrierShiftLinearMap G)
    exact SeparationQuotient.mk_add _ _
  map_smul' := by
    intro r x
    refine Quotient.inductionOn x ?_
    intro F
    change C.separatedShift (P.oneLayerClass (r • F)) =
      r • C.separatedShift (P.oneLayerClass F)
    rw [C.separatedShift_oneLayerClass,
      C.separatedShift_oneLayerClass, map_smul]
    change SeparationQuotient.mk
        (r • C.carrierShiftLinearMap F) =
      r • SeparationQuotient.mk (C.carrierShiftLinearMap F)
    exact SeparationQuotient.mk_smul r _

@[simp] theorem separatedShiftLinearMap_oneLayerClass
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.OneLayerCarrier) :
    C.separatedShiftLinearMap (P.oneLayerClass F) =
      P.oneLayerClass (C.carrierShiftLinearMap F) :=
  C.separatedShift_oneLayerClass F

/-- The descended action remains norm nonincreasing. -/
theorem norm_separatedShiftLinearMap_le
    (C : P.OneLayerShiftedKernelCertificate)
    (x : P.OneLayerSeparated) :
    ‖C.separatedShiftLinearMap x‖ ≤ ‖x‖ := by
  refine Quotient.inductionOn x ?_
  intro F
  have hinner :
      inner ℝ
          (C.separatedShiftLinearMap (P.oneLayerClass F))
          (C.separatedShiftLinearMap (P.oneLayerClass F)) ≤
        inner ℝ (P.oneLayerClass F) (P.oneLayerClass F) := by
    rw [C.separatedShiftLinearMap_oneLayerClass]
    change inner ℝ
        (SeparationQuotient.mk (C.carrierShiftLinearMap F))
        (SeparationQuotient.mk (C.carrierShiftLinearMap F)) ≤
      inner ℝ (SeparationQuotient.mk F) (SeparationQuotient.mk F)
    rw [SeparationQuotient.inner_mk_mk,
      SeparationQuotient.inner_mk_mk,
      real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq]
    nlinarith [C.norm_carrierShiftLinearMap_le F,
      norm_nonneg (C.carrierShiftLinearMap F), norm_nonneg F]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hinner
  exact (sq_le_sq₀
    (norm_nonneg (C.separatedShiftLinearMap (P.oneLayerClass F)))
    (norm_nonneg (P.oneLayerClass F))).mp hinner

/-- The separated shifted-kernel action as a continuous linear contraction. -/
noncomputable def separatedShiftContinuousLinearMap
    (C : P.OneLayerShiftedKernelCertificate) :
    P.OneLayerSeparated →L[ℝ] P.OneLayerSeparated :=
  C.separatedShiftLinearMap.mkContinuous 1 (by
    intro x
    simpa using C.norm_separatedShiftLinearMap_le x)

@[simp] theorem separatedShiftContinuousLinearMap_apply
    (C : P.OneLayerShiftedKernelCertificate)
    (x : P.OneLayerSeparated) :
    C.separatedShiftContinuousLinearMap x = C.separatedShiftLinearMap x :=
  rfl

/-- Symmetry descends to the separated quotient. -/
theorem inner_separatedShiftContinuousLinearMap_left_eq_right
    (C : P.OneLayerShiftedKernelCertificate)
    (x y : P.OneLayerSeparated) :
    inner ℝ (C.separatedShiftContinuousLinearMap x) y =
      inner ℝ x (C.separatedShiftContinuousLinearMap y) := by
  refine Quotient.inductionOn x ?_
  intro F
  refine Quotient.inductionOn y ?_
  intro G
  change inner ℝ
      (C.separatedShiftContinuousLinearMap (P.oneLayerClass F))
      (P.oneLayerClass G) =
    inner ℝ (P.oneLayerClass F)
      (C.separatedShiftContinuousLinearMap (P.oneLayerClass G))
  rw [C.separatedShiftContinuousLinearMap_apply,
    C.separatedShiftContinuousLinearMap_apply,
    C.separatedShiftLinearMap_oneLayerClass,
    C.separatedShiftLinearMap_oneLayerClass]
  change inner ℝ
      (SeparationQuotient.mk (C.carrierShiftLinearMap F))
      (SeparationQuotient.mk G) =
    inner ℝ (SeparationQuotient.mk F)
      (SeparationQuotient.mk (C.carrierShiftLinearMap G))
  rw [SeparationQuotient.inner_mk_mk,
    SeparationQuotient.inner_mk_mk]
  exact C.inner_carrierShiftLinearMap_left_eq_right F G

/-- Positivity descends to the separated quotient. -/
theorem separatedShiftContinuousLinearMap_quadratic_nonneg
    (C : P.OneLayerShiftedKernelCertificate)
    (x : P.OneLayerSeparated) :
    0 ≤ inner ℝ (C.separatedShiftContinuousLinearMap x) x := by
  refine Quotient.inductionOn x ?_
  intro F
  change 0 ≤ inner ℝ
    (C.separatedShiftContinuousLinearMap (P.oneLayerClass F))
    (P.oneLayerClass F)
  rw [C.separatedShiftContinuousLinearMap_apply,
    C.separatedShiftLinearMap_oneLayerClass]
  change 0 ≤ inner ℝ
    (SeparationQuotient.mk (C.carrierShiftLinearMap F))
    (SeparationQuotient.mk F)
  rw [SeparationQuotient.inner_mk_mk]
  exact C.carrierShiftLinearMap_quadratic_nonneg F

/-- The shifted geometric kernel operator on the completed Wilson OS Hilbert
space. -/
noncomputable def hilbertShiftContinuousLinearMap
    (C : P.OneLayerShiftedKernelCertificate) :
    P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert :=
  C.separatedShiftContinuousLinearMap.completion

/-- The completed operator agrees with the separated action on the dense
quotient image. -/
@[simp] theorem hilbertShiftContinuousLinearMap_completedClass
    (C : P.OneLayerShiftedKernelCertificate)
    (x : P.OneLayerSeparated) :
    C.hilbertShiftContinuousLinearMap
        (x : UniformSpace.Completion P.OneLayerSeparated) =
      (C.separatedShiftContinuousLinearMap x :
        UniformSpace.Completion P.OneLayerSeparated) := by
  exact ContinuousLinearMap.completion_apply_coe
    C.separatedShiftContinuousLinearMap x

/-- Inner products of completed separated classes reduce to the separated
inner product. -/
@[simp] theorem inner_completedSeparatedClass
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (x y : P.OneLayerSeparated) :
    inner ℝ
        (x : UniformSpace.Completion P.OneLayerSeparated)
        (y : UniformSpace.Completion P.OneLayerSeparated) =
      inner ℝ x y := by
  exact UniformSpace.Completion.inner_coe x y

/-- On represented carrier states, the completed operator is the original raw
carrier shift. -/
@[simp] theorem hilbertShiftContinuousLinearMap_oneLayerState
    (C : P.OneLayerShiftedKernelCertificate)
    (F : P.OneLayerCarrier) :
    C.hilbertShiftContinuousLinearMap (P.oneLayerState F) =
      P.oneLayerState (C.carrierShiftLinearMap F) := by
  change C.hilbertShiftContinuousLinearMap
      ((P.oneLayerClass F : P.OneLayerSeparated) :
        UniformSpace.Completion P.OneLayerSeparated) =
    ((P.oneLayerClass (C.carrierShiftLinearMap F) : P.OneLayerSeparated) :
      UniformSpace.Completion P.OneLayerSeparated)
  rw [C.hilbertShiftContinuousLinearMap_completedClass,
    C.separatedShiftContinuousLinearMap_apply,
    C.separatedShiftLinearMap_oneLayerClass]

/-- The completed shifted-kernel operator is a contraction. -/
theorem norm_hilbertShiftContinuousLinearMap_le
    (C : P.OneLayerShiftedKernelCertificate)
    (x : P.OneLayerHilbert) :
    ‖C.hilbertShiftContinuousLinearMap x‖ ≤ ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le
      (continuous_norm.comp C.hilbertShiftContinuousLinearMap.continuous)
      continuous_norm) ?_
  intro y
  rw [C.hilbertShiftContinuousLinearMap_completedClass]
  change ‖((C.separatedShiftLinearMap y : P.OneLayerSeparated) :
      UniformSpace.Completion P.OneLayerSeparated)‖ ≤
    ‖((y : P.OneLayerSeparated) :
      UniformSpace.Completion P.OneLayerSeparated)‖
  rw [UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe]
  exact C.norm_separatedShiftLinearMap_le y

/-- Symmetry extends from the separated quotient to the complete Hilbert
carrier. -/
theorem inner_hilbertShiftContinuousLinearMap_left_eq_right
    (C : P.OneLayerShiftedKernelCertificate)
    (x y : P.OneLayerHilbert) :
    inner ℝ (C.hilbertShiftContinuousLinearMap x) y =
      inner ℝ x (C.hilbertShiftContinuousLinearMap y) := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro u v
  change inner ℝ
      (C.hilbertShiftContinuousLinearMap
        (u : UniformSpace.Completion P.OneLayerSeparated))
      (v : UniformSpace.Completion P.OneLayerSeparated) =
    inner ℝ
      (u : UniformSpace.Completion P.OneLayerSeparated)
      (C.hilbertShiftContinuousLinearMap
        (v : UniformSpace.Completion P.OneLayerSeparated))
  rw [C.hilbertShiftContinuousLinearMap_completedClass,
    C.hilbertShiftContinuousLinearMap_completedClass]
  have hleft :
      inner ℝ
          ((C.separatedShiftContinuousLinearMap u : P.OneLayerSeparated) :
            UniformSpace.Completion P.OneLayerSeparated)
          (v : UniformSpace.Completion P.OneLayerSeparated) =
        inner ℝ (C.separatedShiftContinuousLinearMap u) v :=
    UniformSpace.Completion.inner_coe _ _
  have hright :
      inner ℝ
          (u : UniformSpace.Completion P.OneLayerSeparated)
          ((C.separatedShiftContinuousLinearMap v : P.OneLayerSeparated) :
            UniformSpace.Completion P.OneLayerSeparated) =
        inner ℝ u (C.separatedShiftContinuousLinearMap v) :=
    UniformSpace.Completion.inner_coe _ _
  exact hleft.trans
    ((C.inner_separatedShiftContinuousLinearMap_left_eq_right u v).trans
      hright.symm)

/-- Positivity extends to the complete Hilbert carrier. -/
theorem hilbertShiftContinuousLinearMap_quadratic_nonneg
    (C : P.OneLayerShiftedKernelCertificate)
    (x : P.OneLayerHilbert) :
    0 ≤ inner ℝ (C.hilbertShiftContinuousLinearMap x) x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le continuous_const (by fun_prop)) ?_
  intro u
  change 0 ≤ inner ℝ
    (C.hilbertShiftContinuousLinearMap
      (u : UniformSpace.Completion P.OneLayerSeparated))
    (u : UniformSpace.Completion P.OneLayerSeparated)
  rw [C.hilbertShiftContinuousLinearMap_completedClass]
  have hinner :
      inner ℝ
          ((C.separatedShiftContinuousLinearMap u : P.OneLayerSeparated) :
            UniformSpace.Completion P.OneLayerSeparated)
          (u : UniformSpace.Completion P.OneLayerSeparated) =
        inner ℝ (C.separatedShiftContinuousLinearMap u) u :=
    UniformSpace.Completion.inner_coe _ _
  exact hinner.symm ▸ C.separatedShiftContinuousLinearMap_quadratic_nonneg u

/-- The completed operator realizes the independent shifted kernel exactly on
the dense raw-observable image. -/
theorem hilbertShiftContinuousLinearMap_matrixElement
    (C : P.OneLayerShiftedKernelCertificate)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    inner ℝ
        (C.hilbertShiftContinuousLinearMap
          (P.oneLayerObservableEmbedding F))
        (P.oneLayerObservableEmbedding G) =
      finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G := by
  rw [P.oneLayerObservableEmbedding_apply,
    P.oneLayerObservableEmbedding_apply,
    C.hilbertShiftContinuousLinearMap_oneLayerState,
    P.inner_oneLayerState_oneLayerState]
  exact (C.shiftedKernelForm_eq_inner F G).symm

/-- The completed extension is uniquely determined by its dense separated
quotient action. -/
theorem hilbertShiftContinuousLinearMap_unique
    (C : P.OneLayerShiftedKernelCertificate)
    (T : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert)
    (hT : ∀ x : P.OneLayerSeparated,
      T (x : UniformSpace.Completion P.OneLayerSeparated) =
        (C.separatedShiftContinuousLinearMap x :
          UniformSpace.Completion P.OneLayerSeparated)) :
    T = C.hilbertShiftContinuousLinearMap := by
  ext z
  refine UniformSpace.Completion.induction_on z
    (isClosed_eq T.continuous C.hilbertShiftContinuousLinearMap.continuous) ?_
  intro x
  rw [hT x, C.hilbertShiftContinuousLinearMap_completedClass]

/-- Public quotient/completion operator receipt. -/
theorem finiteWilsonOSShiftedKernelHilbertOperatorPackage
    (C : P.OneLayerShiftedKernelCertificate) :
    (∀ x : P.OneLayerHilbert,
      ‖C.hilbertShiftContinuousLinearMap x‖ ≤ ‖x‖) ∧
    (∀ x y : P.OneLayerHilbert,
      inner ℝ (C.hilbertShiftContinuousLinearMap x) y =
        inner ℝ x (C.hilbertShiftContinuousLinearMap y)) ∧
    (∀ x : P.OneLayerHilbert,
      0 ≤ inner ℝ (C.hilbertShiftContinuousLinearMap x) x) ∧
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      inner ℝ
          (C.hilbertShiftContinuousLinearMap
            (P.oneLayerObservableEmbedding F))
          (P.oneLayerObservableEmbedding G) =
        finiteWilsonOSShiftedKernelForm P C.shiftedKernel F G) := by
  exact ⟨C.norm_hilbertShiftContinuousLinearMap_le,
    C.inner_hilbertShiftContinuousLinearMap_left_eq_right,
    C.hilbertShiftContinuousLinearMap_quadratic_nonneg,
    C.hilbertShiftContinuousLinearMap_matrixElement⟩

end OneLayerShiftedKernelCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
