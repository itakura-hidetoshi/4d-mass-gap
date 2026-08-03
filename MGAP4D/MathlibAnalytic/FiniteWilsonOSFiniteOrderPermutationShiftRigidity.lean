import MGAP4D.MathlibAnalytic.FiniteWilsonOSPositiveConfigurationShiftSemigroup
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProduct

noncomputable section

namespace FiniteWilsonOSReflectionPositivityCertificate
namespace PositiveConfigurationShiftCertificate

variable {L : FiniteLatticeWilsonSystem}
  {P : FiniteWilsonOSReflectionPositivityCertificate L}

/-- A finite-order positive-configuration permutation induces the identity at
that period on the completed OS Hilbert space. -/
theorem hilbertShiftSemigroup_eq_identity_of_shift_pow_eq_refl
    (C : P.PositiveConfigurationShiftCertificate)
    (q : ℕ)
    (hperiod : C.shift ^ q = Equiv.refl _) :
    C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup q =
      P.oneLayerIdentityTransfer := by
  apply P.oneLayerOperator_eq_identityTransfer_of_matrixDefect_eq_zero
  intro F G
  apply
    (finiteWilsonOSOneLayerOperatorMatrixDefect_eq_zero_iff
      P.reflectionData P.oneLayerObservableEmbedding
        (C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup q)
        F G).2
  rw [C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup_matrixElement]
  rw [P.inner_eq_wilsonOneLayerTransferForm]
  congr 1
  have hobs := C.carrierShiftIterate_observable q (⟨F⟩ : P.OneLayerCarrier)
  change
    (C.toOneLayerShiftedKernelCertificate.carrierShiftIterate q
      (⟨F⟩ : P.OneLayerCarrier)).observable = F
  rw [hobs]
  funext x
  simp [positiveConfigurationObservableShift, shiftIterate, hperiod]

/-- A symmetric positive contraction whose discrete semigroup has a positive
finite period is necessarily the identity.  This is the Hilbert-space rigidity
behind the obstruction to representing nontrivial Euclidean time by a periodic
configuration permutation. -/
theorem hilbertShiftContinuousLinearMap_eq_identity_of_semigroup_period
    (C : P.OneLayerShiftedKernelCertificate)
    (q : ℕ)
    (hq : 0 < q)
    (hperiod : C.hilbertShiftSemigroup q = P.oneLayerIdentityTransfer) :
    C.hilbertShiftContinuousLinearMap = P.oneLayerIdentityTransfer := by
  let T : P.OneLayerHilbert →L[ℝ] P.OneLayerHilbert :=
    C.hilbertShiftContinuousLinearMap
  have hq_ne : q ≠ 0 := Nat.ne_of_gt hq
  have hq_decomp : q - 1 + 1 = q := by
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq_ne)
  have hnorm (x : P.OneLayerHilbert) : ‖T x‖ = ‖x‖ := by
    apply le_antisymm
    · exact C.norm_hilbertShiftContinuousLinearMap_le x
    · have hback :=
        C.norm_hilbertShiftSemigroup_le (q - 1) (T x)
      have hreturn :
          C.hilbertShiftSemigroup (q - 1) (T x) = x := by
        change
          C.hilbertShiftSemigroup (q - 1)
              (C.hilbertShiftSemigroup 1 x) = x
        rw [← C.hilbertShiftSemigroup_add_apply (q - 1) 1 x,
          hq_decomp, hperiod]
        rfl
      rw [hreturn] at hback
      exact hback
  let U : P.OneLayerHilbert →ₗᵢ[ℝ] P.OneLayerHilbert :=
    { toLinearMap := T.toLinearMap
      norm_map' := hnorm }
  have hinner (x y : P.OneLayerHilbert) :
      inner ℝ (T x) (T y) = inner ℝ x y := by
    exact U.inner_map_map x y
  have hT2 (x : P.OneLayerHilbert) : T (T x) = x := by
    have haa :
        inner ℝ (T (T x)) (T (T x)) = inner ℝ x x := by
      exact (hinner (T x) (T x)).trans (hinner x x)
    have hab : inner ℝ (T (T x)) x = inner ℝ x x := by
      calc
        inner ℝ (T (T x)) x = inner ℝ (T x) (T x) :=
          C.inner_hilbertShiftContinuousLinearMap_left_eq_right (T x) x
        _ = inner ℝ x x := hinner x x
    have hba : inner ℝ x (T (T x)) = inner ℝ x x := by
      rw [real_inner_comm]
      exact hab
    have hzero :
        inner ℝ (T (T x) - x) (T (T x) - x) = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
        haa, hab, hba]
      ring
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hzero)
  apply ContinuousLinearMap.ext
  intro x
  rw [P.oneLayerIdentityTransfer_apply]
  let y : P.OneLayerHilbert := T x - x
  have hTy : T y = -y := by
    dsimp [y]
    rw [map_sub, hT2]
    module
  have hpos := C.hilbertShiftContinuousLinearMap_quadratic_nonneg y
  rw [hTy, inner_neg_left] at hpos
  have hself_nonneg : 0 ≤ inner ℝ y y := real_inner_self_nonneg
  have hself_zero : inner ℝ y y = 0 := by
    linarith
  have hy : y = 0 := inner_self_eq_zero.mp hself_zero
  exact sub_eq_zero.mp hy

/-- Finite-order rigidity stated directly for a concrete positive-configuration
shift certificate. -/
theorem hilbertShiftContinuousLinearMap_eq_identity_of_shift_pow_eq_refl
    (C : P.PositiveConfigurationShiftCertificate)
    (q : ℕ)
    (hq : 0 < q)
    (hperiod : C.shift ^ q = Equiv.refl _) :
    C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap =
      P.oneLayerIdentityTransfer := by
  apply
    C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap_eq_identity_of_semigroup_period
      q hq
  exact C.hilbertShiftSemigroup_eq_identity_of_shift_pow_eq_refl q hperiod

/-- Consequently, a finite-order permutation certificate cannot also carry a
nonidentity Wilson action witness. -/
theorem no_wilsonAction_witness_of_finite_order_shift
    (C : P.PositiveConfigurationShiftCertificate)
    (q : ℕ)
    (hq : 0 < q)
    (hperiod : C.shift ^ q = Equiv.refl _)
    (hBeta : L.beta ≠ 0) :
    ¬ ∃ x y : P.reflectionData.PositiveConfiguration,
      L.wilsonAction (P.reflectionData.assemble (C.shift x) y) ≠
        L.wilsonAction (P.reflectionData.assemble x y) := by
  rintro ⟨x, y, hAction⟩
  have hIdentity :=
    C.hilbertShiftContinuousLinearMap_eq_identity_of_shift_pow_eq_refl
      q hq hperiod
  exact
    (C.hilbertShiftContinuousLinearMap_ne_identity_of_wilsonAction_ne
      x y hBeta hAction) hIdentity

/-- Public finite-order permutation rigidity receipt. -/
theorem finiteWilsonOSFiniteOrderPermutationShiftRigidityPackage
    (C : P.PositiveConfigurationShiftCertificate)
    (q : ℕ)
    (hq : 0 < q)
    (hperiod : C.shift ^ q = Equiv.refl _) :
    C.toOneLayerShiftedKernelCertificate.hilbertShiftSemigroup q =
        P.oneLayerIdentityTransfer ∧
      C.toOneLayerShiftedKernelCertificate.hilbertShiftContinuousLinearMap =
        P.oneLayerIdentityTransfer := by
  exact ⟨C.hilbertShiftSemigroup_eq_identity_of_shift_pow_eq_refl q hperiod,
    C.hilbertShiftContinuousLinearMap_eq_identity_of_shift_pow_eq_refl
      q hq hperiod⟩

end PositiveConfigurationShiftCertificate
end FiniteWilsonOSReflectionPositivityCertificate

end

end MathlibAnalytic
end MGAP4D
