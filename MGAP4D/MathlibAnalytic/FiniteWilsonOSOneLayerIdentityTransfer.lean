import MGAP4D.MathlibAnalytic.FiniteWilsonOSOneLayerHilbertCompletion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate

variable {L : FiniteLatticeWilsonSystem}

/-- The canonical bounded operator represented by the currently available
Wilson one-layer form on its own OS Hilbert completion.  Because that form is
also the Hilbert inner product, the represented operator is the identity. -/
noncomputable def oneLayerIdentityTransfer
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert :=
  1

@[simp] theorem oneLayerIdentityTransfer_apply
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (x : P.OneLayerHilbert) :
    P.oneLayerIdentityTransfer x = x := by
  rfl

/-- The canonical identity transfer reproduces every Wilson one-layer matrix
element on the dense raw-observable image. -/
theorem oneLayerIdentityTransfer_matrixElement
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    inner ℝ
        (P.oneLayerIdentityTransfer (P.oneLayerObservableEmbedding F))
        (P.oneLayerObservableEmbedding G) =
      P.reflectionData.wilsonOneLayerTransferForm F G := by
  rw [P.oneLayerIdentityTransfer_apply,
    P.inner_oneLayerObservableEmbedding]

/-- The matrix-element defect of the identity transfer vanishes identically. -/
@[simp] theorem oneLayerIdentityTransfer_matrixDefect_eq_zero
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (F G : P.reflectionData.PositiveConfiguration → ℝ) :
    finiteWilsonOSOneLayerOperatorMatrixDefect
        P.reflectionData P.oneLayerObservableEmbedding
          P.oneLayerIdentityTransfer F G = 0 := by
  apply
    (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
      P.reflectionData P.oneLayerObservableEmbedding
        P.oneLayerIdentityTransfer F G).2
  exact P.oneLayerIdentityTransfer_matrixElement F G

/-- If a bounded operator reproduces all Wilson one-layer matrix elements, then
it fixes every represented observable vector. -/
theorem oneLayerOperator_fixes_observableEmbedding_of_matrixDefect_eq_zero
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert)
    (hD : ∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0)
    (F : P.reflectionData.PositiveConfiguration → ℝ) :
    candidate (P.oneLayerObservableEmbedding F) =
      P.oneLayerObservableEmbedding F := by
  let d : P.OneLayerHilbert :=
    candidate (P.oneLayerObservableEmbedding F) -
      P.oneLayerObservableEmbedding F
  have horth : ∀ y : P.OneLayerHilbert, inner ℝ d y = 0 := by
    intro y
    refine P.oneLayerObservableEmbedding_denseRange.induction_on ?_ ?_ y
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro G
      change
        inner ℝ
            (candidate (P.oneLayerObservableEmbedding F) -
              P.oneLayerObservableEmbedding F)
            (P.oneLayerObservableEmbedding G) = 0
      rw [inner_sub_left]
      have hFG :=
        (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
          P.reflectionData P.oneLayerObservableEmbedding candidate F G).mp
          (hD F G)
      rw [hFG, P.inner_oneLayerObservableEmbedding]
      simp
  have hself : inner ℝ d d = 0 := horth d
  have hnormsq : ‖d‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    exact hself
  have hnorm : ‖d‖ = 0 := by
    nlinarith [norm_nonneg d]
  have hd : d = 0 := norm_eq_zero.mp hnorm
  exact sub_eq_zero.mp hd

/-- Density and continuity make the identity transfer the unique bounded
operator reproducing the complete Wilson one-layer form. -/
theorem oneLayerOperator_eq_identityTransfer_of_matrixDefect_eq_zero
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert)
    (hD : ∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0) :
    candidate = P.oneLayerIdentityTransfer := by
  apply ContinuousLinearMap.ext
  intro x
  refine P.oneLayerObservableEmbedding_denseRange.induction_on ?_ ?_ x
  · exact isClosed_eq candidate.continuous P.oneLayerIdentityTransfer.continuous
  · intro F
    rw [P.oneLayerIdentityTransfer_apply]
    exact P.oneLayerOperator_fixes_observableEmbedding_of_matrixDefect_eq_zero
      candidate hD F

/-- Exact uniqueness equivalence: all geometric one-layer matrix defects vanish
if and only if the candidate is the canonical identity transfer. -/
theorem oneLayerOperator_all_matrixDefects_eq_zero_iff
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert) :
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0) ↔
      candidate = P.oneLayerIdentityTransfer := by
  constructor
  · exact P.oneLayerOperator_eq_identityTransfer_of_matrixDefect_eq_zero candidate
  · intro hCandidate F G
    rw [hCandidate]
    exact P.oneLayerIdentityTransfer_matrixDefect_eq_zero F G

/-- A nonidentity candidate has an explicit nonzero geometric matrix-element
defect. -/
theorem oneLayerOperator_exists_matrixDefect_ne_zero_of_ne_identity
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert)
    (hCandidate : candidate ≠ P.oneLayerIdentityTransfer) :
    ∃ F G : P.reflectionData.PositiveConfiguration → ℝ,
      finiteWilsonOSOneLayerOperatorMatrixDefect
        P.reflectionData P.oneLayerObservableEmbedding candidate F G ≠ 0 := by
  by_contra h
  push_neg at h
  apply hCandidate
  exact P.oneLayerOperator_eq_identityTransfer_of_matrixDefect_eq_zero
    candidate h

@[simp] theorem oneLayerIdentityTransfer_pow
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (n : ℕ) :
    P.oneLayerIdentityTransfer ^ n = 1 := by
  simp [oneLayerIdentityTransfer]

/-- Every natural power of the canonical transfer fixes the entire Hilbert
carrier. -/
@[simp] theorem oneLayerIdentityTransfer_pow_apply
    (P : FiniteWilsonOSReflectionPositivityCertificate L)
    (n : ℕ) (x : P.OneLayerHilbert) :
    (P.oneLayerIdentityTransfer ^ n) x = x := by
  rw [P.oneLayerIdentityTransfer_pow]
  rfl

/-- Symmetry, nonnegative quadratic form, and isometry/contraction receipts for
the canonical geometric one-layer transfer. -/
theorem oneLayerIdentityTransfer_operator_receipt
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    (∀ x y : P.OneLayerHilbert,
      inner ℝ (P.oneLayerIdentityTransfer x) y =
        inner ℝ x (P.oneLayerIdentityTransfer y)) ∧
    (∀ x : P.OneLayerHilbert,
      0 ≤ inner ℝ (P.oneLayerIdentityTransfer x) x) ∧
    (∀ x : P.OneLayerHilbert,
      ‖P.oneLayerIdentityTransfer x‖ = ‖x‖) := by
  constructor
  · intro x y
    simp
  constructor
  · intro x
    simp only [P.oneLayerIdentityTransfer_apply]
    exact real_inner_self_nonneg
  · intro x
    simp

/-- Public identity-obstruction package: the one-layer OS form has a canonical
Hilbert completion, is represented by the identity, and uniquely determines
that identity among bounded operators. -/
theorem finiteWilsonOSOneLayerIdentityTransferPackage
    (P : FiniteWilsonOSReflectionPositivityCertificate L) :
    (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
      inner ℝ
          (P.oneLayerIdentityTransfer (P.oneLayerObservableEmbedding F))
          (P.oneLayerObservableEmbedding G) =
        P.reflectionData.wilsonOneLayerTransferForm F G) ∧
    (∀ candidate : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert,
      (∀ F G : P.reflectionData.PositiveConfiguration → ℝ,
        finiteWilsonOSOneLayerOperatorMatrixDefect
          P.reflectionData P.oneLayerObservableEmbedding candidate F G = 0) ↔
        candidate = P.oneLayerIdentityTransfer) ∧
    (∀ n : ℕ, P.oneLayerIdentityTransfer ^ n = 1) := by
  exact ⟨P.oneLayerIdentityTransfer_matrixElement,
    P.oneLayerOperator_all_matrixDefects_eq_zero_iff,
    P.oneLayerIdentityTransfer_pow⟩

end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
