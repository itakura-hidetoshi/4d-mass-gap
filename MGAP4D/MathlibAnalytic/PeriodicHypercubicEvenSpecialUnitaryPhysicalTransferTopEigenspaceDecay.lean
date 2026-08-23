import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- A zero-safe midpoint contraction factor associated with a strict bounded
endomorphism contraction.  Using `(1 + ‖R‖) / 2` keeps the factor strictly
positive even when `R = 0`, while retaining a strict factor below one whenever
`‖R‖ < 1`. -/
noncomputable def realContinuousLinearMapStrictContractionMidpointFactor
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E) : ℝ :=
  (1 + ‖R‖) / 2

/-- The midpoint factor is strictly positive. -/
theorem realContinuousLinearMapStrictContractionMidpointFactor_pos
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E) :
    0 < realContinuousLinearMapStrictContractionMidpointFactor R := by
  have hnorm : 0 ≤ ‖R‖ := norm_nonneg R
  dsimp [realContinuousLinearMapStrictContractionMidpointFactor]
  linarith

/-- A strict operator contraction gives a midpoint factor strictly below one. -/
theorem realContinuousLinearMapStrictContractionMidpointFactor_lt_one
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ < 1) :
    realContinuousLinearMapStrictContractionMidpointFactor R < 1 := by
  dsimp [realContinuousLinearMapStrictContractionMidpointFactor]
  linarith

/-- The original operator norm lies below its midpoint contraction factor. -/
theorem realContinuousLinearMap_norm_le_strictContractionMidpointFactor
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ < 1) :
    ‖R‖ ≤ realContinuousLinearMapStrictContractionMidpointFactor R := by
  dsimp [realContinuousLinearMapStrictContractionMidpointFactor]
  linarith

/-- Submultiplicativity iterated through natural powers of a bounded real
endomorphism. -/
theorem realContinuousLinearMap_pow_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (n : ℕ) :
    ‖R ^ n‖ ≤ ‖R‖ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact
        (norm_mul_le (R ^ n) R).trans
          (mul_le_mul_of_nonneg_right ih (norm_nonneg R))

/-- Powers of a strict bounded contraction are geometrically controlled by the
zero-safe midpoint factor. -/
theorem realContinuousLinearMapStrictContraction_pow_norm_le_midpointFactor
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ < 1)
    (n : ℕ) :
    ‖R ^ n‖ ≤
      (realContinuousLinearMapStrictContractionMidpointFactor R) ^ n := by
  have hnormle := realContinuousLinearMap_norm_le_strictContractionMidpointFactor R hR
  have hqnonneg : 0 ≤ realContinuousLinearMapStrictContractionMidpointFactor R :=
    (realContinuousLinearMapStrictContractionMidpointFactor_pos R).le
  calc
    ‖R ^ n‖ ≤ ‖R‖ ^ n := realContinuousLinearMap_pow_norm_le R n
    _ ≤ (realContinuousLinearMapStrictContractionMidpointFactor R) ^ n := by
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, pow_succ]
          exact mul_le_mul ih hnormle (norm_nonneg R) (pow_nonneg hqnonneg n)

/-- Pointwise geometric decay follows from the operator-power estimate. -/
theorem realContinuousLinearMapStrictContraction_pow_apply_norm_le_midpointFactor
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ < 1)
    (n : ℕ)
    (x : E) :
    ‖(R ^ n) x‖ ≤
      (realContinuousLinearMapStrictContractionMidpointFactor R) ^ n * ‖x‖ := by
  calc
    ‖(R ^ n) x‖ ≤ ‖R ^ n‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (R ^ n) x
    _ ≤ (realContinuousLinearMapStrictContractionMidpointFactor R) ^ n * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (realContinuousLinearMapStrictContraction_pow_norm_le_midpointFactor R hR n)
        (norm_nonneg x)

/-- A finite positive decay rate associated canonically with the midpoint
factor of a strict contraction. -/
noncomputable def realContinuousLinearMapStrictContractionMidpointRate
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E) : ℝ :=
  -Real.log (realContinuousLinearMapStrictContractionMidpointFactor R)

/-- Strict contraction makes the midpoint logarithmic decay rate positive. -/
theorem realContinuousLinearMapStrictContractionMidpointRate_pos
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E)
    (hR : ‖R‖ < 1) :
    0 < realContinuousLinearMapStrictContractionMidpointRate R := by
  dsimp [realContinuousLinearMapStrictContractionMidpointRate]
  exact neg_pos.mpr
    (Real.log_neg
      (realContinuousLinearMapStrictContractionMidpointFactor_pos R)
      (realContinuousLinearMapStrictContractionMidpointFactor_lt_one R hR))

/-- The midpoint factor is exactly the exponential of minus its logarithmic
rate. -/
theorem realContinuousLinearMapStrictContractionMidpointFactor_eq_exp_neg_rate
    {E : Type u}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (R : E →L[ℝ] E) :
    realContinuousLinearMapStrictContractionMidpointFactor R =
      Real.exp (-realContinuousLinearMapStrictContractionMidpointRate R) := by
  have hqpos := realContinuousLinearMapStrictContractionMidpointFactor_pos R
  dsimp [realContinuousLinearMapStrictContractionMidpointRate]
  rw [neg_neg, Real.exp_log hqpos]

/-- Canonical finite-volume contraction factor for the normalized physical
transfer on the orthogonal complement of its full top eigenspace. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  realContinuousLinearMapStrictContractionMidpointFactor
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta)

/-- The actual finite-volume decay factor is positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta := by
  exact realContinuousLinearMapStrictContractionMidpointFactor_pos _

/-- The actual finite-volume decay factor is strictly below one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta < 1 := by
  exact realContinuousLinearMapStrictContractionMidpointFactor_lt_one _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta)

/-- Natural powers of the actual excitation transfer decay geometrically in
operator norm. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n := by
  exact realContinuousLinearMapStrictContraction_pow_norm_le_midpointFactor _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta) n

/-- Every vector in the top-eigenspace orthogonal sector obeys the same
finite-volume geometric time-step decay. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n * ‖f‖ := by
  exact realContinuousLinearMapStrictContraction_pow_apply_norm_le_midpointFactor _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta) n f

/-- Canonical positive finite-volume logarithmic transfer decay scale.  It is
not a volume-uniform or continuum mass-gap statement. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  realContinuousLinearMapStrictContractionMidpointRate
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta)

/-- The finite-volume logarithmic transfer decay scale is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta := by
  exact realContinuousLinearMapStrictContractionMidpointRate_pos _
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta)

/-- The finite-volume geometric decay factor is exactly `exp (-m_fv)` for the
canonical logarithmic decay scale. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_eq_exp_neg_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta =
      Real.exp
        (-periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) := by
  exact realContinuousLinearMapStrictContractionMidpointFactor_eq_exp_neg_rate _

/-- Audit-visible finite-volume geometric decay package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  decayFactorPositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta
  decayFactorStrict :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta < 1
  powerNormDecay : ∀ n : ℕ,
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n
  vectorDecay : ∀ (n : ℕ)
      (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta),
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n * ‖f‖
  finiteVolumeDecayRatePositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  decayFactorExponential :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta =
      Real.exp
        (-periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)

/-- Construct the actual finite-volume geometric decay package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayPackage
      H N hN beta hbeta :=
  { decayFactorPositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pos
        H N hN beta hbeta
    decayFactorStrict :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_lt_one
        H N hN beta hbeta
    powerNormDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le
        H N hN beta hbeta
    vectorDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le
        H N hN beta hbeta
    finiteVolumeDecayRatePositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta
    decayFactorExponential :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_eq_exp_neg_finiteVolumeDecayRate
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D
