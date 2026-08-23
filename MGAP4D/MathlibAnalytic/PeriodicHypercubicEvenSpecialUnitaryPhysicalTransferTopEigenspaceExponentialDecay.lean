import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Natural powers of the canonical finite-volume decay factor are exactly
exponentials of the positive finite-volume logarithmic rate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pow_eq_exp_neg_nat_mul_finiteVolumeDecayRate
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta) ^ n =
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_eq_exp_neg_finiteVolumeDecayRate]
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring

/-- The actual excitation-transfer powers obey exponential operator-norm decay
with the positive finite-volume logarithmic rate. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_exp_of_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) (hn : 0 < n) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) := by
  calc
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ n :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_of_pos
        H N hN beta hbeta n hn
    _ = Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pow_eq_exp_neg_nat_mul_finiteVolumeDecayRate
        H N hN beta hbeta n

/-- Every excitation vector obeys the corresponding exponential norm decay at
positive integer Euclidean times. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) (hn : 0 < n)
    (f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖ := by
  calc
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
          H N hN beta hbeta) ^ n * ‖f‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_of_pos
        H N hN beta hbeta n hn f
    _ = Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖ := by
      rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pow_eq_exp_neg_nat_mul_finiteVolumeDecayRate]

/-- Finite-volume Euclidean-time matrix coefficients between excitation
vectors decay with the same positive logarithmic rate.  The inner product is
read in the already-established Gauss-law Hilbert carrier, avoiding any new
Hilbert structure on the named orthogonal subtype. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_matrixCoefficient_norm_le_exp_of_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (n : ℕ) (hn : 0 < n)
    (f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
      H N hN beta hbeta) :
    ‖inner ℝ
        (((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
      (Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖) * ‖g‖ := by
  have hCS :
      ‖inner ℝ
          (((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            H N hN beta hbeta) ^ n) f :
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
                H N hN beta hbeta) :
            periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
          (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
        ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f‖ * ‖g‖ := by
    simpa using
      (norm_inner_le_norm
        (((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
  exact hCS.trans
    (mul_le_mul_of_nonneg_right
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
        H N hN beta hbeta n hn f)
      (norm_nonneg g))

/-- Audit-visible finite-volume exponential Euclidean-time decay package. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceExponentialDecayPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : Prop where
  finiteVolumeRatePositive :
    0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  factorPowerExponential : ∀ n : ℕ,
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor
      H N hN beta hbeta) ^ n =
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta)
  operatorExponentialDecay : ∀ (n : ℕ), 0 < n →
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n‖ ≤
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta)
  vectorExponentialDecay : ∀ (n : ℕ), 0 < n →
      ∀ f : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      H N hN beta hbeta) ^ n) f‖ ≤
      Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖
  matrixCoefficientExponentialDecay : ∀ (n : ℕ), 0 < n →
      ∀ f g : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H N hN beta hbeta,
    ‖inner ℝ
        (((((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H N hN beta hbeta) ^ n) f :
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
              H N hN beta hbeta) :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N))
        (g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)‖ ≤
      (Real.exp
        (-(n : ℝ) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
            H N hN beta hbeta) * ‖f‖) * ‖g‖

/-- Construct the actual finite-volume exponential time-decay package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceExponentialDecayPackage
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceExponentialDecayPackage
      H N hN beta hbeta :=
  { finiteVolumeRatePositive :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate_pos
        H N hN beta hbeta
    factorPowerExponential :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceDecayFactor_pow_eq_exp_neg_nat_mul_finiteVolumeDecayRate
        H N hN beta hbeta
    operatorExponentialDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_norm_le_exp_of_pos
        H N hN beta hbeta
    vectorExponentialDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_pow_apply_norm_le_exp_of_pos
        H N hN beta hbeta
    matrixCoefficientExponentialDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_matrixCoefficient_norm_le_exp_of_pos
        H N hN beta hbeta }

end

end MathlibAnalytic
end MGAP4D