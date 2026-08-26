import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

universe u

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- Scalar extension respects composition of bounded real physical operators. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_comp
    (H N : ℕ)
    (T U : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N (T.comp U) =
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T).comp
        (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N U) := by
  apply ContinuousLinearMap.ext
  intro f
  apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
  · simp [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]
  · simp [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]

local instance periodicHypercubicEvenSpecialUnitaryComplexPowerCFCRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexPowerCFCComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The normalized complex transfer absorbs the isolated CFC top projection on
the right. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H N hN beta hbeta
  have hReal :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_comp_topSpectralProjection
      H N hN beta hbeta
  have hcomp :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N S).comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_comp]
    exact congrArg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N)
      (by simpa [S, P] using hReal)
  rw [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification]
  apply ContinuousLinearMap.ext
  intro f
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N S
        (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P f
  exact congrArg (fun T => T f) hcomp

/-- The isolated CFC top projection absorbs the normalized complex transfer on
the right. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_normalizedTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta := by
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H N hN beta hbeta
  have hReal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection_comp_normalizedTransferOperator
      H N hN beta hbeta
  have hcomp :
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P).comp
          (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N S) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_comp]
    exact congrArg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N)
      (by simpa [S, P] using hReal)
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator]
  apply ContinuousLinearMap.ext
  intro f
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P
        (periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N S f) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N P f
  exact congrArg (fun T => T f) hcomp

/-- The isolated CFC top element is idempotent in the bounded-operator algebra. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_isStarProjection
    H N hN beta hbeta).isIdempotentElem.eq

/-- The centered complex transfer annihilates the CFC top sector on the right. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mul_cfcTopProjection
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta = 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator,
    sub_mul,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_cfcTopProjection,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self,
    sub_self]

/-- The CFC top sector annihilates the centered complex transfer on the right. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_centeredTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta = 0 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator,
    mul_sub,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_normalizedTransferOperator,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self,
    sub_self]

/-- Orthogonal idempotent and residual summands have completely separated
positive powers. -/
theorem idempotent_add_orthogonal_pow_succ
    {A : Type u} [Ring A]
    (p r : A)
    (hpp : p * p = p)
    (hpr : p * r = 0)
    (hrp : r * p = 0)
    (n : ℕ) :
    (p + r) ^ (n + 1) = p + r ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrpowp : r ^ (n + 1) * p = 0 := by
        rw [pow_succ, mul_assoc, hrp, mul_zero]
      calc
        (p + r) ^ (Nat.succ n + 1) = (p + r) ^ (n + 1) * (p + r) := by
          rw [show Nat.succ n + 1 = (n + 1) + 1 by omega, pow_succ]
        _ = (p + r ^ (n + 1)) * (p + r) := by rw [ih]
        _ = p + r ^ (Nat.succ n + 1) := by
          rw [add_mul, mul_add, mul_add, hpp, hpr, hrpowp]
          simp [pow_succ]

/-- Every positive power of the genuine normalized complex Wilson transfer is
the full CFC top projection plus the corresponding centered power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_eq_cfcTop_add_centered_pow
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^ (n + 1) =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta +
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) ^ (n + 1) := by
  let S := periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let P := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
    H N hN beta hbeta
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  have hdecomp : S = P + R := by
    simp [S, P, R,
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator]
  have hPP : P * P = P := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_self
        H N hN beta hbeta
  have hPR : P * R = 0 := by
    simpa [P, R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_centeredTransferOperator
        H N hN beta hbeta
  have hRP : R * P = 0 := by
    simpa [P, R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_mul_cfcTopProjection
        H N hN beta hbeta
  change S ^ (n + 1) = P + R ^ (n + 1)
  rw [hdecomp]
  exact idempotent_add_orthogonal_pow_succ P R hPP hPR hRP n

/-- Exact residual identity after removing the isolated CFC top projection from
a positive transfer power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_eq_centered_pow
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta) ^ (n + 1) -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) ^ (n + 1) := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_eq_cfcTop_add_centered_pow]
  abel

/-- Quantitative operator-norm convergence of normalized complex transfer powers
to the isolated CFC top projection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1) -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_eq_centered_pow]
  exact
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_pow_norm_le
      H N hN beta hbeta (n + 1)

/-- Pointwise quantitative convergence of every positive normalized complex
transfer power to the CFC top component. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_apply_sub_cfcTop_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1)) f -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ := by
  have hop :=
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_norm_le
      H N hN beta hbeta n
  let D :=
    (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1) -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta
  calc
    ‖((periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1)) f -
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta f‖ = ‖D f‖ := by rfl
    _ ≤ ‖D‖ * ‖f‖ := ContinuousLinearMap.le_opNorm D f
    _ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1) * ‖f‖ := by
      exact mul_le_mul_of_nonneg_right (by simpa [D] using hop) (norm_nonneg f)

/-- Audit-visible package for exact top-plus-centered decomposition and geometric
convergence of positive complex transfer powers. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPowerCFCConvergencePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  topAbsorbsTransfer :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta
  transferAbsorbsTop :
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta *
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
        H N hN beta hbeta
  powerDecomposition :
    ∀ n : ℕ,
      (periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta) ^ (n + 1) =
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta +
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
          H N hN beta hbeta) ^ (n + 1)
  geometricConvergence :
    ∀ n : ℕ,
      ‖(periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta) ^ (n + 1) -
        periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
          H N hN beta hbeta‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ (n + 1)

/-- Construct the transfer-power CFC convergence package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPowerCFCConvergencePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTransferPowerCFCConvergencePackage
      H N hN beta hbeta :=
  { topAbsorbsTransfer :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_mul_normalizedTransferOperator
        H N hN beta hbeta
    transferAbsorbsTop :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_mul_cfcTopProjection
        H N hN beta hbeta
    powerDecomposition :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_eq_cfcTop_add_centered_pow
        H N hN beta hbeta
    geometricConvergence :=
      periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator_pow_succ_sub_cfcTop_norm_le
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D