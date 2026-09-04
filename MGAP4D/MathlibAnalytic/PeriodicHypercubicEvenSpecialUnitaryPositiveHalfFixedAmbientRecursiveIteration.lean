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
              omega
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
              rw [pow_succ']
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
              omega
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
              rw [pow_succ']
        _ =
          ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
              H N hN beta hbeta) ^ Nat.succ m)
            (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
              H 1 N hN beta hbeta) := by
              rfl

end

end MathlibAnalytic
end MGAP4D
