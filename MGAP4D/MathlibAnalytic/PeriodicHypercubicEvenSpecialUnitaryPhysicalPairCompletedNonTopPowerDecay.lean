import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance physicalPairCompletedNonTopPowerDecayTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalPairCompletedNonTopPowerDecayCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalPairCompletedNonTopPowerDecaySecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalPairCompletedNonTopPowerDecayMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalPairCompletedNonTopPowerDecayBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance physicalPairCompletedNonTopPowerDecaySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalPairCompletedNonTopPowerDecaySpatialSliceHaarSFinite (H N : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

section PowerDecay

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "PairE" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2 H N
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H N hN beta hbeta
local notation "S₂" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator H N hN beta hbeta
local notation "NN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure H N hN beta hbeta
local notation "SN" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator H N hN beta hbeta

/-- Powers of the bundled completed non-top restriction are exactly the
restrictions of the corresponding ambient normalized pair-transfer powers. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_coe_apply
    (k : ℕ) (x : NN) :
    (((SN ^ k) x : NN) : PairE) = (S₂ ^ k) (x : PairE) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      change
        (((SN ^ k) (SN x) : NN) : PairE) =
          (S₂ ^ k) (S₂ (x : PairE))
      calc
        (((SN ^ k) (SN x) : NN) : PairE) =
            (S₂ ^ k) (((SN x : NN) : PairE)) := ih (SN x)
        _ = (S₂ ^ k) (S₂ (x : PairE)) := by
          rw [periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_coe_apply]

/-- Pointwise geometric decay for powers of the bundled completed non-top
restriction.  The proof is inductive and therefore does not require a
`NormOneClass` instance on the continuous-linear-map endomorphism algebra. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_apply_norm_le
    (k : ℕ) (x : NN) :
    ‖(SN ^ k) x‖ ≤ ‖R‖ ^ k * ‖x‖ := by
  have hq0 : 0 ≤ ‖R‖ := norm_nonneg R
  have hSN : ∀ y : NN, ‖SN y‖ ≤ ‖R‖ * ‖y‖ := by
    intro y
    calc
      ‖SN y‖ ≤ ‖SN‖ * ‖y‖ := ContinuousLinearMap.le_opNorm SN y
      _ ≤ ‖R‖ * ‖y‖ :=
        mul_le_mul_of_nonneg_right
          (periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_le
            H N hN beta hbeta)
          (norm_nonneg y)
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      change
        ‖(SN ^ k) (SN x)‖ ≤ ‖R‖ ^ Nat.succ k * ‖x‖
      calc
        ‖(SN ^ k) (SN x)‖ ≤ ‖R‖ ^ k * ‖SN x‖ := ih (SN x)
        _ ≤ ‖R‖ ^ k * (‖R‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (hSN x) (pow_nonneg hq0 k)
        _ = ‖R‖ ^ Nat.succ k * ‖x‖ := by
          rw [pow_succ]
          ring

/-- The `k`th power of the completed non-top restriction has operator norm at
most the `k`th power of the one-slice orthogonal contraction factor. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_norm_le
    (k : ℕ) :
    ‖SN ^ k‖ ≤ ‖R‖ ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound (SN ^ k) (pow_nonneg (norm_nonneg R) k)
  intro x
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_apply_norm_le
      H N hN beta hbeta k x

/-- Ambient form of the finite-volume power decay: every vector in the
completed physical non-top sector decays geometrically under normalized pair
transfer with factor `q = ‖R‖`. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
    (k : ℕ) (x : PairE) (hx : x ∈ NN) :
    ‖(S₂ ^ k) x‖ ≤ ‖R‖ ^ k * ‖x‖ := by
  let xN : NN := ⟨x, hx⟩
  have hpow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_coe_apply
      H N hN beta hbeta k xN
  calc
    ‖(S₂ ^ k) x‖ = ‖(SN ^ k) xN‖ := by
      rw [← hpow]
      rfl
    _ ≤ ‖R‖ ^ k * ‖xN‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_apply_norm_le
        H N hN beta hbeta k xN
    _ = ‖R‖ ^ k * ‖x‖ := rfl

/-- The geometric factor controlling every completed non-top power is strictly
below one at finite volume. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one :
    ‖R‖ < 1 :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
    H N hN beta hbeta

/-- Audit-visible finite-volume arbitrary-power decay package for the completed
physical non-top pair sector.  It assumes neither top-eigenspace simplicity nor
vacuum uniqueness, and makes no scale-uniform or infinite-volume claim. -/
structure PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopPowerDecayPackage :
    Prop where
  restrictedPowerNorm :
    ∀ k : ℕ, ‖SN ^ k‖ ≤ ‖R‖ ^ k
  restrictedPowerPointwise :
    ∀ (k : ℕ) (x : NN), ‖(SN ^ k) x‖ ≤ ‖R‖ ^ k * ‖x‖
  ambientPowerCorrespondence :
    ∀ (k : ℕ) (x : NN),
      (((SN ^ k) x : NN) : PairE) = (S₂ ^ k) (x : PairE)
  ambientPowerDecay :
    ∀ (k : ℕ) (x : PairE), x ∈ NN →
      ‖(S₂ ^ k) x‖ ≤ ‖R‖ ^ k * ‖x‖
  factorStrict : ‖R‖ < 1
  restrictedStrict : ‖SN‖ < 1

/-- Construct the finite-volume completed physical non-top arbitrary-power
decay package. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopPowerDecayPackage :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalPairCompletedNonTopPowerDecayPackage
      H N hN beta hbeta :=
  { restrictedPowerNorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_norm_le
        H N hN beta hbeta
    restrictedPowerPointwise :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_apply_norm_le
        H N hN beta hbeta
    ambientPowerCorrespondence :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_pow_coe_apply
        H N hN beta hbeta
    ambientPowerDecay :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopBlockClosure_normalizedTransfer_pow_norm_le
        H N hN beta hbeta
    factorStrict :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopPowerDecay_factor_lt_one
        H N hN beta hbeta
    restrictedStrict :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPairNonTopTransferOperator_norm_lt_one
        H N hN beta hbeta }

end PowerDecay

end

end MathlibAnalytic
end MGAP4D
