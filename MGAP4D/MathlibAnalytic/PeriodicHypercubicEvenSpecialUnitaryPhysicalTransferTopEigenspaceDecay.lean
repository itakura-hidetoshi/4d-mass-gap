import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceContraction
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

universe u

/-- A zero-safe midpoint contraction factor for a nonnegative scalar bound.
Using `(1 + r) / 2` keeps the factor strictly positive even when `r = 0`,
while retaining a strict factor below one whenever `r < 1`. -/
noncomputable def realStrictContractionMidpointFactor (r : ℝ) : ℝ :=
  (1 + r) / 2

/-- A nonnegative scalar bound has strictly positive midpoint factor. -/
theorem realStrictContractionMidpointFactor_pos
    {r : ℝ}
    (hr0 : 0 ≤ r) :
    0 < realStrictContractionMidpointFactor r := by
  dsimp [realStrictContractionMidpointFactor]
  linarith

/-- A strict scalar contraction has midpoint factor strictly below one. -/
theorem realStrictContractionMidpointFactor_lt_one
    {r : ℝ}
    (hr : r < 1) :
    realStrictContractionMidpointFactor r < 1 := by
  dsimp [realStrictContractionMidpointFactor]
  linarith

/-- A strict scalar contraction is bounded by its midpoint factor. -/
theorem real_le_strictContractionMidpointFactor
    {r : ℝ}
    (hr : r < 1) :
    r ≤ realStrictContractionMidpointFactor r := by
  dsimp [realStrictContractionMidpointFactor]
  linarith

/-- Powers preserve the comparison with the midpoint contraction factor. -/
theorem real_pow_le_strictContractionMidpointFactor_pow
    {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr : r < 1)
    (n : ℕ) :
    r ^ n ≤ (realStrictContractionMidpointFactor r) ^ n := by
  have hrle : r ≤ realStrictContractionMidpointFactor r :=
    real_le_strictContractionMidpointFactor hr
  have hq0 : 0 ≤ realStrictContractionMidpointFactor r :=
    (realStrictContractionMidpointFactor_pos hr0).le
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hrle hr0 (pow_nonneg hq0 n)

/-- The positive logarithmic rate associated with the midpoint factor. -/
noncomputable def realStrictContractionMidpointRate (r : ℝ) : ℝ :=
  -Real.log (realStrictContractionMidpointFactor r)

/-- A nonnegative strict scalar contraction has positive logarithmic rate. -/
theorem realStrictContractionMidpointRate_pos
    {r : ℝ}
    (hr0 : 0 ≤ r)
    (hr : r < 1) :
    0 < realStrictContractionMidpointRate r := by
  dsimp [realStrictContractionMidpointRate]
  exact neg_pos.mpr
    (Real.log_neg
      (realStrictContractionMidpointFactor_pos hr0)
      (realStrictContractionMidpointFactor_lt_one hr))

/-- The midpoint factor is exactly the exponential of minus its logarithmic
rate. -/
theorem realStrictContractionMidpointFactor_eq_exp_neg_rate
    {r : ℝ}
    (hr0 : 0 ≤ r) :
    realStrictContractionMidpointFactor r =
      Real.exp (-realStrictContractionMidpointRate r) := by
  have hqpos : 0 < realStrictContractionMidpointFactor r :=
    realStrictContractionMidpointFactor_pos hr0
  dsimp [realStrictContractionMidpointRate]
  rw [neg_neg, Real.exp_log hqpos]

/-- In the generic Hilbert carrier, the power of the top-eigenspace orthogonal
restriction obeys its bundled operator-norm bound pointwise.  Keeping this
lemma at the ambient Hilbert level avoids `NormedSpace` reconstruction for
an already bundled concrete subtype operator. -/
theorem realHilbertTopEigenspaceOrthogonalRestriction_pow_apply_norm_le
    {E : Type u}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hS : (S : E →ₗ[ℝ] E).IsSymmetric)
    (n : ℕ)
    (f : (realHilbertTopEigenspace S)ᗮ) :
    ‖((realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ n) f‖ ≤
      ‖(realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ n‖ * ‖f‖ := by
  exact ContinuousLinearMap.le_opNorm _ _

/-- Canonical finite-volume contraction factor for the normalized physical
transfer on the orthogonal complement of its full top eigenspace. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  realStrictContractionMidpointFactor
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖

/-- The actual finite-volume decay factor is positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta := by
  change 0 < realStrictContractionMidpointFactor
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  exact realStrictContractionMidpointFactor_pos
    (norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta))

/-- The actual finite-volume decay factor is strictly below one. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_lt_one
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta < 1 := by
  exact realStrictContractionMidpointFactor_lt_one
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H N hN beta hbeta)

/-- Positive natural powers of the actual excitation transfer decay
geometrically in operator norm.  The positive-step formulation avoids making
any nontriviality assumption on the excitation sector at time zero. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_of_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) (hn : 0 < n) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta
  have hRlt : ‖R‖ < 1 := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
        H N hN beta hbeta
  calc
    ‖R ^ n‖ ≤ ‖R‖ ^ n := norm_pow_le' R hn
    _ ≤ (realStrictContractionMidpointFactor ‖R‖) ^ n :=
      real_pow_le_strictContractionMidpointFactor_pow (norm_nonneg R) hRlt n
    _ = (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ n := by
      simp [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor, R]

/-- Every vector in the top-eigenspace orthogonal sector obeys the same
finite-volume geometric bound at each positive time step. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) (hn : 0 < n)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n * ‖f‖ := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let hS : (S :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N).IsSymmetric := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        H N hN beta hbeta
  have hApply :=
    realHilbertTopEigenspaceOrthogonalRestriction_pow_apply_norm_le S hS n f
  calc
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
        ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n‖ * ‖f‖ := by
      change
        ‖((realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ n) f‖ ≤
          ‖(realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ n‖ * ‖f‖
      exact hApply
    _ ≤ (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ n * ‖f‖ :=
      mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_of_pos
          H N hN beta hbeta n hn)
        (norm_nonneg f)

/-- Canonical positive finite-volume logarithmic transfer decay scale.  It is
not a volume-uniform or continuum mass-gap statement. -/
noncomputable def periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  realStrictContractionMidpointRate
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖

/-- The finite-volume logarithmic transfer decay scale is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta := by
  change 0 < realStrictContractionMidpointRate
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta‖
  exact realStrictContractionMidpointRate_pos
    (norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta))
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
  change realStrictContractionMidpointFactor
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta‖ =
    Real.exp
      (-realStrictContractionMidpointRate
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta‖)
  exact realStrictContractionMidpointFactor_eq_exp_neg_rate
    (norm_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H N hN beta hbeta))

/-- Audit-visible finite-volume top-eigenspace geometric decay package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  decayFactorPositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta
  decayFactorStrict :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta < 1
  powerNormDecay : ∀ (n : ℕ), 0 < n →
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
        H N hN beta hbeta) ^ n
  vectorDecay : ∀ (n : ℕ), 0 < n →
      ∀ f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_of_pos
        H N hN beta hbeta
    vectorDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
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