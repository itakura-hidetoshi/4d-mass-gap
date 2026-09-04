import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveIteration
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabPairHaarL2TransferContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfFixedAmbientRecursiveNormContractionIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfFixedAmbientRecursiveNormContractionCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfFixedAmbientRecursiveNormContractionSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfFixedAmbientRecursiveNormContractionMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfFixedAmbientRecursiveNormContractionBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance positiveHalfFixedAmbientRecursiveNormContractionSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- One fixed-ambient pair step cannot increase the pair-Haar `L²` norm of the
recursive inward message. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_norm_le
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R + 2) N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta‖ := by
  have hstep :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_eq_pairTransferOperator
      H R N hN beta hbeta
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R + 2) N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta)‖ := by
            simpa using congrArg norm hstep
    _ ≤
      ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
          H N hN beta hbeta‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta‖ :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator
        H N hN beta hbeta).le_opNorm _
    _ ≤ 1 *
        ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
          H R N hN beta hbeta‖ := by
      exact mul_le_mul_of_nonneg_right
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabPairTransferOperator_norm_le_one
          H N hN beta hbeta)
        (norm_nonneg _)
    _ =
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta‖ := by
      simp

/-- Any finite number of fixed-ambient pair steps is norm-contracting on the
recursive inward messages. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_mul_norm_le
    (H R k N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R + 2 * k) N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta‖ := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep :=
        periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_norm_le
          H (R + 2 * k) N hN beta hbeta
      calc
        ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (R + 2 * Nat.succ k) N hN beta hbeta‖ =
          ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H ((R + 2 * k) + 2) N hN beta hbeta‖ := by
              exact congrArg
                (fun r =>
                  ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                    H r N hN beta hbeta‖)
                (by omega)
        _ ≤
          ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H (R + 2 * k) N hN beta hbeta‖ := hstep
        _ ≤
          ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
            H R N hN beta hbeta‖ := ih

/-- Every fixed-ambient recursive message is norm-bounded by its parity terminal
message (`R = 0` for even depth and `R = 1` for odd depth). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_norm_le_terminal_mod_two
    (H R N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta‖ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R % 2) N hN beta hbeta‖ := by
  have hbound :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2_add_two_mul_norm_le
      H (R % 2) (R / 2) N hN beta hbeta
  calc
    ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H R N hN beta hbeta‖ =
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R % 2 + 2 * (R / 2)) N hN beta hbeta‖ := by
          exact congrArg
            (fun r =>
              ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
                H r N hN beta hbeta‖)
            (by omega)
    _ ≤
      ‖periodicHypercubicEvenSpecialUnitaryPositiveHalfFixedAmbientRecursiveHaarMessageL2
        H (R % 2) N hN beta hbeta‖ := hbound

end

end MathlibAnalytic
end MGAP4D
