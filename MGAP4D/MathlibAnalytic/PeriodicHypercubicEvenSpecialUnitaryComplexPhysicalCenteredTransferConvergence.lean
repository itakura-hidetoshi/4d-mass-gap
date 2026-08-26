import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalTopCFCProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Module End Set
open scoped InnerProductSpace InnerProduct Ring Topology

noncomputable section

universe u

set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 750000

/-- Subtracting the canonical fixed-space projection from a symmetric real
Hilbert-space operator has exactly the norm of its restriction to the
fixed-space orthogonal complement. -/
theorem realHilbertCenteredOperator_norm_eq_orthogonalRestriction
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric) :
    ‖S - realHilbertTopEigenspaceProjection S‖ =
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hS‖ := by
  let F := realHilbertTopEigenspace S
  let P := realHilbertTopEigenspaceProjection S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F :=
    (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ :=
    F.isClosed_orthogonal.completeSpace_coe
  change
    sInf { c : ℝ | 0 ≤ c ∧ ∀ x : E, ‖(S - P) x‖ ≤ c * ‖x‖ } =
      sInf { c : ℝ | 0 ≤ c ∧ ∀ y : Fᗮ, ‖R y‖ ≤ c * ‖y‖ }
  apply congrArg sInf
  ext c
  constructor
  · rintro ⟨hc0, hc⟩
    refine ⟨hc0, ?_⟩
    intro y
    have hyOrth : (y : E) ∈ (realHilbertTopEigenspace S)ᗮ := by
      simpa [F] using y.property
    have hPy : P (y : E) = 0 := by
      exact (realHilbertTopEigenspaceProjection_apply_eq_zero_iff S (y : E)).2 hyOrth
    have h := hc (y : E)
    have hcenter : (S - P) (y : E) = S (y : E) := by
      simp [hPy]
    have hR : ‖R y‖ = ‖S (y : E)‖ := by
      rfl
    rw [hcenter, ← hR] at h
    simpa using h
  · rintro ⟨hc0, hc⟩
    refine ⟨hc0, ?_⟩
    intro x
    have hPxMem : P x ∈ F := by
      simpa [P, F, realHilbertTopEigenspaceProjection] using
        F.starProjection_apply_mem x
    have hSPx : S (P x) = P x := by
      exact (realHilbertTopEigenspace_mem S (P x)).1 (by simpa [F] using hPxMem)
    have hzOrth : x - P x ∈ Fᗮ := by
      simpa [P, F, realHilbertTopEigenspaceProjection] using
        F.sub_starProjection_mem_orthogonal x
    let z : Fᗮ := ⟨x - P x, hzOrth⟩
    have hzNorm : ‖z‖ ≤ ‖x‖ := by
      have h := (Fᗮ).norm_starProjection_apply_le x
      have horthApply : Fᗮ.starProjection x = x - F.starProjection x := by
        have horth := congrArg (fun T : E →L[ℝ] E => T x)
          (Submodule.starProjection_orthogonal F)
        simpa using horth
      rw [horthApply] at h
      simpa [z, P, F, realHilbertTopEigenspaceProjection] using h
    have hcenter : (S - P) x = S (z : E) := by
      change S x - P x = S (x - P x)
      rw [map_sub, hSPx]
    have hR : ‖R z‖ = ‖S (z : E)‖ := by
      rfl
    calc
      ‖(S - P) x‖ = ‖R z‖ := by rw [hcenter, hR]
      _ ≤ c * ‖z‖ := hc z
      _ ≤ c * ‖x‖ := mul_le_mul_of_nonneg_left hzNorm hc0

/-- Scalar extension respects subtraction of bounded real physical operators. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_sub
    (H N : ℕ)
    (T U : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →L[ℝ]
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N (T - U) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N T -
        periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N U := by
  apply ContinuousLinearMap.ext
  intro f
  apply periodicHypercubicEvenSpecialUnitaryComplexPhysical_ext_components H N
  · simp [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]
  · simp [periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_apply]

local instance periodicHypercubicEvenSpecialUnitaryComplexCenteredTransferRealCompleteSpace
    (H N : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H N).completeSpace_coe

local instance periodicHypercubicEvenSpecialUnitaryComplexCenteredTransferComplexCompleteSpace
    (H N : ℕ) :
    CompleteSpace (PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :=
  periodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert_completeSpace H N

/-- The genuine complex normalized Wilson transfer with its isolated CFC top
sector removed. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N →L[ℂ]
      PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta -
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection
      H N hN beta hbeta

/-- The centered complex transfer is exactly the scalar extension of the real
normalized transfer with its canonical full-top projection removed. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_eq_complexification
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
            H N hN beta hbeta) := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator,
    periodicHypercubicEvenSpecialUnitaryComplexNormalizedPhysicalOneSlabTransferOperator,
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCFCTopSpectralProjection_eq_complexification,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_sub]

/-- Exact operator norm of the centered complex transfer: no loss occurs when
passing from the genuine real excited restriction to the complex physical
carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta‖ =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖ := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_eq_complexification,
    periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification_norm]
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator] using
    (realHilbertCenteredOperator_norm_eq_orthogonalRestriction
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta))

/-- The CFC-centered complex transfer is a strict contraction. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta‖ < 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta

/-- Powers in the bounded-operator algebra obey the geometric operator-norm
bound supplied by the exact centered norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_pow_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ n := by
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  have hnorm :
      ‖R‖ =
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
        H N hN beta hbeta
  have hpow : ‖R ^ n‖ ≤ ‖R‖ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact (norm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right ih (norm_nonneg R))
  simpa [R, hnorm] using hpow

/-- Pointwise geometric decay of every centered transfer power. -/
theorem
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_pow_apply_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (n : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalHilbert H N) :
    ‖((periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ ^ n * ‖f‖ := by
  let R := periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
    H N hN beta hbeta
  calc
    ‖(R ^ n) f‖ ≤ ‖R ^ n‖ * ‖f‖ := ContinuousLinearMap.le_opNorm (R ^ n) f
    _ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ n * ‖f‖ := by
      exact mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_pow_norm_le
          H N hN beta hbeta n)
        (norm_nonneg f)

/-- Audit-visible package for the quantitative centered complex transfer
contraction obtained from the isolated CFC top projection. -/
structure PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergencePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  centeredIsComplexification :
    periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta =
      periodicHypercubicEvenSpecialUnitaryPhysicalOperatorComplexification H N
        (periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
            H N hN beta hbeta)
  exactCenteredNorm :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta‖ =
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  strictContraction :
    ‖periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
      H N hN beta hbeta‖ < 1
  geometricPowers :
    ∀ n : ℕ,
      ‖(periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator
        H N hN beta hbeta) ^ n‖ ≤
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖ ^ n

/-- Construct the exact centered-transfer convergence package. -/
theorem periodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergencePackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryComplexPhysicalCenteredTransferConvergencePackage
      H N hN beta hbeta :=
  { centeredIsComplexification :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_eq_complexification
        H N hN beta hbeta
    exactCenteredNorm :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_eq_real_excited
        H N hN beta hbeta
    strictContraction :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_norm_lt_one
        H N hN beta hbeta
    geometricPowers :=
      periodicHypercubicEvenSpecialUnitaryComplexPhysicalOneSlabCenteredTransferOperator_pow_norm_le
        H N hN beta hbeta }

end
end MathlibAnalytic
end MGAP4D