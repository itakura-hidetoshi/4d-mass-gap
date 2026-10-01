import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialUniformGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopEigenspaceDecay
import Mathlib.Tactic

/-!
# Scale-uniform geometric decay on the physical top-orthogonal sectors

PR #4982 proves the explicit all-scale transfer-gap lower bound

  1/3072 <= gap_n = 1 - ||R_n||

for the normalized one-slab transfer restricted to the full physical
top-eigenspace orthogonal sector, on one positive volume/rank-independent
high-temperature interval.

This file converts that gap statement into the exact geometric form needed by
the thermodynamic/common-carrier limit routes.

Define the common contraction factor

  q0 = 3071/3072.

Then every finite scale satisfies

  ||R_n|| <= q0 < 1,

hence every positive natural power and every excitation vector satisfy

  ||R_n^k|| <= q0^k,
  ||R_n^k x|| <= q0^k ||x||.

The coefficient q0 is independent of lattice volume, gauge rank, and scale.
No continuum-time interpolation or finite-volume embedding compatibility is
asserted here; those are the next H1 layer.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped InnerProductSpace

noncomputable section

namespace GroundStateSourceFixedPairEnergy

/-- Explicit common contraction factor furnished by the #4982 uniform gap. -/
def twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor : ℝ :=
  3071 / 3072

theorem twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_pos :
    0 < twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor := by
  norm_num [twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor]

theorem twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_nonneg :
    0 ≤ twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor :=
  twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_pos.le

theorem twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_lt_one :
    twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor < 1 := by
  norm_num [twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor]

/-- Positive logarithmic rate associated with the explicit common contraction
factor. -/
def twoSidedTwelveSpatialUniformTopOrthogonalDecayRate : ℝ :=
  -Real.log twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor

theorem twoSidedTwelveSpatialUniformTopOrthogonalDecayRate_pos :
    0 < twoSidedTwelveSpatialUniformTopOrthogonalDecayRate := by
  unfold twoSidedTwelveSpatialUniformTopOrthogonalDecayRate
  exact neg_pos.mpr
    (Real.log_neg
      twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_pos
      twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_lt_one)

theorem twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_eq_exp_neg_rate :
    twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor =
      Real.exp (-twoSidedTwelveSpatialUniformTopOrthogonalDecayRate) := by
  unfold twoSidedTwelveSpatialUniformTopOrthogonalDecayRate
  rw [neg_neg, Real.exp_log
    twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_pos]

end GroundStateSourceFixedPairEnergy

private theorem real_pow_le_pow_of_nonneg_of_le
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (k : ℕ) :
    a ^ k ≤ b ^ k := by
  have hb : 0 ≤ b := ha.trans hab
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hab ha (pow_nonneg hb k)

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- #4982 rewritten as a uniform one-step operator-norm contraction on every
physical top-orthogonal finite-volume sector. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor := by
  have hgap :=
    periodicHypercubicEvenSpecialUnitary_uniformTopEigenspaceTransferGap_ge_one_div_3072
      halfExtent N hN beta hbeta s hs hcut n
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap]
    at hgap
  unfold
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  nlinarith

/-- Every positive natural power of the finite-volume top-orthogonal transfer
has the same scale-independent geometric operator-norm bound. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ)
    (hk : 0 < k) :
    ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k := by
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  let q :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  have hR0 : 0 ≤ ‖R‖ := norm_nonneg R
  have hRq : ‖R‖ ≤ q := by
    simpa [R, q] using
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
        halfExtent N hN beta hbeta s hs hcut n
  calc
    ‖R ^ k‖ ≤ ‖R‖ ^ k := norm_pow_le' R hk
    _ ≤ q ^ k :=
      real_pow_le_pow_of_nonneg_of_le hR0 hRq k
    _ = _ := rfl

/-- Uniform geometric decay for every vector in every physical
top-eigenspace-orthogonal finite-volume sector. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_apply_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (n k : ℕ)
    (hk : 0 < k)
    (x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        (halfExtent n) N hN (beta n) (hbeta n)) :
    ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖x‖ := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  let hS : (S :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N →ₗ[ℝ]
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
          (halfExtent n) N).IsSymmetric := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
        (halfExtent n) N hN (beta n) (hbeta n)
  let R :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
      (halfExtent n) N hN (beta n) (hbeta n)
  have hApply :=
    realHilbertTopEigenspaceOrthogonalRestriction_pow_apply_norm_le S hS k x
  have hOp :
      ‖R ^ k‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k := by
    simpa [R] using
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk
  calc
    ‖(R ^ k) x‖ ≤ ‖R ^ k‖ * ‖x‖ := by
      change
        ‖((realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k) x‖ ≤
          ‖(realHilbertTopEigenspaceOrthogonalRestriction S hS) ^ k‖ * ‖x‖
      exact hApply
    _ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
          ‖x‖ :=
      mul_le_mul_of_nonneg_right hOp (norm_nonneg x)
    _ = _ := rfl

/-- Audit-visible package for the first H1 bridge: one volume/rank/scale
independent geometric contraction factor controls all finite-volume
top-orthogonal one-step transfers and their positive natural powers. -/
structure PeriodicHypercubicEvenSpecialUnitaryUniformTopOrthogonalPowerDecayPackage : Prop where
  factorPositive :
    0 <
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  factorStrict :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor < 1
  oneStep :
    ∀ n : ℕ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
  powerNorm :
    ∀ (n k : ℕ), 0 < k →
      ‖(periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          (halfExtent n) N hN (beta n) (hbeta n)) ^ k‖ ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k
  vectorDecay :
    ∀ (n k : ℕ), 0 < k →
      ∀ x :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          (halfExtent n) N hN (beta n) (hbeta n),
        ‖((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
            (halfExtent n) N hN (beta n) (hbeta n)) ^ k) x‖ ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
            ‖x‖
  ratePositive :
    0 <
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalDecayRate
  factorExponential :
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor =
      Real.exp
        (-GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalDecayRate)

/-- Construct the H1-ready uniform natural-power decay package directly from
the certified #4982 high-temperature family cutoff. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalPowerDecayPackage
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    PeriodicHypercubicEvenSpecialUnitaryUniformTopOrthogonalPowerDecayPackage
      halfExtent N hN beta hbeta := by
  refine
    { factorPositive :=
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_pos
      factorStrict :=
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_lt_one
      oneStep := ?_
      powerNorm := ?_
      vectorDecay := ?_
      ratePositive :=
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalDecayRate_pos
      factorExponential :=
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_eq_exp_neg_rate }
  · intro n
    exact
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_norm_le
        halfExtent N hN beta hbeta s hs hcut n
  · intro n k hk
    exact
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk
  · intro n k hk x
    exact
      periodicHypercubicEvenSpecialUnitary_uniformTopOrthogonalTransferOperator_pow_apply_norm_le
        halfExtent N hN beta hbeta s hs hcut n k hk x

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
