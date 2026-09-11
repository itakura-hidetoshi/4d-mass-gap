import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveOperator
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientRecursiveIterationIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveIterationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveIterationSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveIterationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveIterationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveIterationSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Even remaining inward-chain lengths are exactly iterates of the ambient
pair transfer operator applied to the literal `R = 0` terminal message. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_even_eq_pairTransferOperator_pow_zero
    (H m N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (2 * m) N hN beta hbeta =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ m)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H 0 N hN beta hbeta) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      let T :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
      have hstep :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_eq_pairTransferOperator
          H (2 * m) N hN beta hbeta
      calc
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (2 * Nat.succ m) N hN beta hbeta =
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (2 * m + 2) N hN beta hbeta := by
              congr 1
        _ = T
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H (2 * m) N hN beta hbeta) := by
              simpa [T] using hstep
        _ = T
            ((T ^ m)
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                H 0 N hN beta hbeta)) := by
              rw [ih]
        _ = (T ^ Nat.succ m)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H 0 N hN beta hbeta) := by
              rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        _ =
          ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta) ^ Nat.succ m)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H 0 N hN beta hbeta) := by
              rfl

/-- Odd remaining inward-chain lengths are exactly iterates of the ambient pair
transfer operator applied to the diagonal-central `R = 1` terminal message. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_odd_eq_pairTransferOperator_pow_one
    (H m N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (2 * m + 1) N hN beta hbeta =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ m)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H 1 N hN beta hbeta) := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      let T :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
      have hstep :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_eq_pairTransferOperator
          H (2 * m + 1) N hN beta hbeta
      calc
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (2 * Nat.succ m + 1) N hN beta hbeta =
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H ((2 * m + 1) + 2) N hN beta hbeta := by
              congr 1
        _ = T
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H (2 * m + 1) N hN beta hbeta) := by
              simpa [T] using hstep
        _ = T
            ((T ^ m)
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                H 1 N hN beta hbeta)) := by
              rw [ih]
        _ = (T ^ Nat.succ m)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H 1 N hN beta hbeta) := by
              rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        _ =
          ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta) ^ Nat.succ m)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H 1 N hN beta hbeta) := by
              rfl

/-- Every fixed-ambient recursive Haar message has one parity-uniform normal
form: iterate the ambient pair transfer operator `R / 2` times, then stop at
the unique terminal message indexed by `R % 2` (`0` or `1`). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_eq_pairTransferOperator_pow_div_two_mod_two
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ (R / 2))
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H (R % 2) N hN beta hbeta) := by
  have hmod : R % 2 = 0 ∨ R % 2 = 1 := by
    omega
  rcases hmod with hzero | hone
  · have hR : R = 2 * (R / 2) := by
      omega
    calc
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta =
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H (2 * (R / 2)) N hN beta hbeta := by
            exact congrArg
              (fun r =>
                periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                  H r N hN beta hbeta)
              hR
      _ =
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta) ^ (R / 2))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H 0 N hN beta hbeta) := by
              simpa using
                (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_even_eq_pairTransferOperator_pow_zero
                  H (R / 2) N hN beta hbeta)
      _ =
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta) ^ (R / 2))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (R % 2) N hN beta hbeta) := by
              rw [hzero]
  · have hR : R = 2 * (R / 2) + 1 := by
      omega
    calc
      periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta =
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H (2 * (R / 2) + 1) N hN beta hbeta := by
            exact congrArg
              (fun r =>
                periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                  H r N hN beta hbeta)
              hR
      _ =
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta) ^ (R / 2))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H 1 N hN beta hbeta) := by
              simpa using
                (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_odd_eq_pairTransferOperator_pow_one
                  H (R / 2) N hN beta hbeta)
      _ =
        ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
            H N hN beta hbeta) ^ (R / 2))
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (R % 2) N hN beta hbeta) := by
              rw [hone]

/-- Advancing any fixed-ambient inward chain by `2 * k` slices is exactly the
`k`-fold iterate of the same ambient pair transfer operator.  This is the
semigroup form of the recursive transfer law, with no restriction on the
starting parity of `R`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_mul_eq_pairTransferOperator_pow
    (H R k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R + 2 * k) N hN beta hbeta =
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta) ^ k)
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      let T :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
      have hstep :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_eq_pairTransferOperator
          H (R + 2 * k) N hN beta hbeta
      calc
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (R + 2 * Nat.succ k) N hN beta hbeta =
          periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H ((R + 2 * k) + 2) N hN beta hbeta := by
              exact congrArg
                (fun r =>
                  periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                    H r N hN beta hbeta)
                (by omega)
        _ = T
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H (R + 2 * k) N hN beta hbeta) := by
              simpa [T] using hstep
        _ = T
            ((T ^ k)
              (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                H R N hN beta hbeta)) := by
              rw [ih]
        _ = (T ^ Nat.succ k)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H R N hN beta hbeta) := by
              rw [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
        _ =
          ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta) ^ Nat.succ k)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H R N hN beta hbeta) := by
              rfl

end

end MathlibAnalytic
end MGAP4D
