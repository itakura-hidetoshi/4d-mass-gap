import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUnitReceiverPointwiseFiberWitness
import Mathlib.Tactic

/-!
# P4-Q2-I: original positive-beta Wilson crossing forces true receiver variation

The exact uncentered physical constant receiver is
  J_beta(A,B) = C_beta(B) / sqrt(W_beta(A,B)),
where W_beta is the canonical continuous representative of the ORIGINAL Wilson
joint density and C_beta(B) contains the ORIGINAL normalized physical transfer
acting on the physical constant unit vector. This is a genuine pointwise
identity of continuous versions, never an L2 quotient evaluation.

We first prove a scalar four-corner square-root crossing lemma. Its physical
specialization combines the original strictly positive SU(2) Wilson crossing
minor, P4-Q2-H full-support right-link descent, and one explicit nonvanishing
physical constant-transfer value. There is no substitution of the
vacuum-density nonmeasurability for constant-receiver nonmeasurability.

The remaining separate analytic task is to discharge that explicit
nonvanishing hypothesis using the strict positivity of the original
finite-volume Wilson kernel integral of constant one.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Pure scalar crossing obstruction: a strictly positive 2x2 determinant
cannot be compatible with BOTH rows of a right-column-weighted
reciprocal-square-root kernel being independent of the column. Only one
column weight is required to be nonzero. -/
theorem p4Q2_crossing_forces_one_row_receiver_difference
    (w11 w12 w21 w22 c1 c2 : ℝ)
    (hw11 : 0 < w11) (hw12 : 0 < w12)
    (hw21 : 0 < w21) (hw22 : 0 < w22)
    (hc1 : c1 ≠ 0)
    (hminor : 0 < w11 * w22 - w12 * w21) :
    c1 / Real.sqrt w11 ≠ c2 / Real.sqrt w12 ∨
      c1 / Real.sqrt w21 ≠ c2 / Real.sqrt w22 := by
  by_contra hn
  push Not at hn
  obtain ⟨hrow1, hrow2⟩ := hn
  have h11 : Real.sqrt w11 ≠ 0 := (Real.sqrt_pos.2 hw11).ne'
  have h12 : Real.sqrt w12 ≠ 0 := (Real.sqrt_pos.2 hw12).ne'
  have h21 : Real.sqrt w21 ≠ 0 := (Real.sqrt_pos.2 hw21).ne'
  have h22 : Real.sqrt w22 ≠ 0 := (Real.sqrt_pos.2 hw22).ne'
  have hfirst : c1 * Real.sqrt w12 = c2 * Real.sqrt w11 :=
    (div_eq_div_iff h11 h12).mp hrow1
  have hsecond : c1 * Real.sqrt w22 = c2 * Real.sqrt w21 :=
    (div_eq_div_iff h21 h22).mp hrow2
  have hsfirst : c1 ^ 2 * w12 = c2 ^ 2 * w11 := by
    have hs := congrArg (fun x : ℝ => x ^ 2) hfirst
    simpa only [mul_pow, Real.sq_sqrt hw12.le, Real.sq_sqrt hw11.le] using hs
  have hssecond : c1 ^ 2 * w22 = c2 ^ 2 * w21 := by
    have hs := congrArg (fun x : ℝ => x ^ 2) hsecond
    simpa only [mul_pow, Real.sq_sqrt hw22.le, Real.sq_sqrt hw21.le] using hs
  have hzero : c1 ^ 2 * (w11 * w22 - w12 * w21) = 0 := by
    calc
      c1 ^ 2 * (w11 * w22 - w12 * w21) =
          w11 * (c1 ^ 2 * w22) - w21 * (c1 ^ 2 * w12) := by ring
      _ = w11 * (c2 ^ 2 * w21) - w21 * (c2 ^ 2 * w11) := by
        rw [hssecond, hsfirst]
      _ = 0 := by ring
  have hdet : w11 * w22 - w12 * w21 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero 2 hc1)
  exact (ne_of_gt hminor) hdet

local instance p4Q2MinorGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2MinorCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2MinorSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2MinorMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2MinorBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2MinorSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4Q2MinorTargetLinkFintype
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H e) :=
  Subtype.fintype (fun i : PeriodicHypercubicEvenSpatialSliceLink H => i = e)

namespace GroundStatePosteriorJoint

/-- Exact pointwise cancellation of the continuous joint half-density:
the true receiver is a right-only signed transfer coefficient divided
by the positive square-root of the ORIGINAL canonical Wilson joint
density, without a posterior replacement. -/
theorem originalPhysicalConstantUnitReceiver_eq_rightFactor_div_sqrtWilson
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (Nat.zero_lt_succ 1)
        beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
        (A,B) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (Nat.zero_lt_succ 1) beta hbeta‖⁻¹ *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H 2 (Nat.zero_lt_succ 1) beta hbeta B *
        normalizedPhysicalOneSlabVacuumReceiverBCF H 2 (Nat.zero_lt_succ 1)
          beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B) /
        Real.sqrt (originalWilsonContinuousPhysicalJointWeight H beta hbeta (A,B)) := by
  have hW :
      continuousJointWeight H 2 (Nat.zero_lt_succ 1) beta hbeta (A,B) =
        originalWilsonContinuousPhysicalJointWeight H beta hbeta (A,B) := by
    unfold continuousJointWeight originalWilsonContinuousPhysicalJointWeight
    ring
  rw [normalizedPhysicalOneSlabJointReceiverProductBCF_apply]
  change
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (Nat.zero_lt_succ 1) beta hbeta‖⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (Nat.zero_lt_succ 1) beta hbeta B *
      normalizedPhysicalOneSlabVacuumReceiverBCF H 2 (Nat.zero_lt_succ 1)
        beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) B) /
      Real.sqrt (continuousJointWeight H 2 (Nat.zero_lt_succ 1) beta hbeta (A,B)) =
    _
  rw [hW]

/-- Positive-beta crossing of the ACTUAL original Wilson physical density
forces strict positive original constant-receiver loss as soon as the
ORIGINAL normalized physical transfer of the constant input has a
nonzero value at the explicit identity boundary.

This theorem isolates one concrete, checkable analytic nonvanishing
obligation, rather than falsely identifying it with Wilson-vacuum
non-retention. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_pos_of_explicitConstantTransfer_ne_zero
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (hM :
      normalizedPhysicalOneSlabVacuumReceiverBCF H 2 (Nat.zero_lt_succ 1)
        beta (le_of_lt hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
        (originalWilsonExplicitIdentityBoundary H) ≠ 0) :
    0 < physicalOriginalUnitReceiverFullLinkEnergy H 2 (Nat.zero_lt_succ 1)
      beta (le_of_lt hbeta) := by
  classical
  let A := originalWilsonExplicitIdentityBoundary H
  let B := originalWilsonExplicitRotatedBoundary H
  let e := originalWilsonExplicitSpatialTargetLink H
  let split :=
    periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
      (Gauge := Matrix.specialUnitaryGroup (Fin 2) ℂ) e
  let W := originalWilsonContinuousPhysicalJointWeight H beta (le_of_lt hbeta)
  let J := normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (Nat.zero_lt_succ 1)
    beta (le_of_lt hbeta)
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
  let C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 → ℝ :=
    fun R =>
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta)‖⁻¹ *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) R *
      normalizedPhysicalOneSlabVacuumReceiverBCF H 2 (Nat.zero_lt_succ 1)
        beta (le_of_lt hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) R
  have hJ : ∀ L R, J (L,R) = C R / Real.sqrt (W (L,R)) := by
    intro L R
    exact originalPhysicalConstantUnitReceiver_eq_rightFactor_div_sqrtWilson
      H beta (le_of_lt hbeta) L R
  have hWA : 0 < W (A,A) :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta (le_of_lt hbeta) (A,A)
  have hWAB : 0 < W (A,B) :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta (le_of_lt hbeta) (A,B)
  have hWBA : 0 < W (B,A) :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta (le_of_lt hbeta) (B,A)
  have hWB : 0 < W (B,B) :=
    originalWilsonContinuousPhysicalJointWeight_pos H beta (le_of_lt hbeta) (B,B)
  have hminor : 0 < W (A,A) * W (B,B) - W (A,B) * W (B,A) := by
    change 0 < originalWilsonContinuousPhysicalJointTwoByTwoMinor H beta
      (le_of_lt hbeta) A B A B
    exact originalWilsonContinuousPhysicalJoint_explicitMinor_pos H beta hbeta
  have hlambda :
      0 < ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta)‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta)
  have hOmega :
      0 < periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H 2 (Nat.zero_lt_succ 1) beta (le_of_lt hbeta) A
  have hC : C A ≠ 0 :=
    mul_ne_zero (mul_ne_zero
      (ne_of_gt (inv_pos.mpr hlambda)) (ne_of_gt hOmega)) hM
  have hrows :
      C A / Real.sqrt (W (A,A)) ≠ C B / Real.sqrt (W (A,B)) ∨
      C A / Real.sqrt (W (B,A)) ≠ C B / Real.sqrt (W (B,B)) :=
    p4Q2_crossing_forces_one_row_receiver_difference
      (W (A,A)) (W (A,B)) (W (B,A)) (W (B,B))
      (C A) (C B) hWA hWAB hWBA hWB hC hminor
  have hoff : (split B).2 = (split A).2 := by
    funext i
    change B i.1 = A i.1
    have hi : (i : PeriodicHypercubicEvenSpatialSliceLink H) ≠ e := i.property
    simp [B, A, originalWilsonExplicitRotatedBoundary,
      originalWilsonExplicitIdentityBoundary, e, hi]
  have hA : split.symm ((split A).1, (split A).2) = A :=
    split.symm_apply_apply A
  have hB : split.symm ((split B).1, (split A).2) = B := by
    rw [← hoff]
    exact split.symm_apply_apply B
  rcases hrows with hrow | hrow
  · have hdifference : J (A,A) ≠ J (A,B) := by
      simpa only [hJ] using hrow
    apply physicalOriginalUnitReceiverFullLinkEnergy_pos_of_targetFiber_difference
      H beta hbeta A (split A).2 (split A).1 (split B).1
    change J (A, split.symm ((split A).1, (split A).2)) ≠
      J (A, split.symm ((split B).1, (split A).2))
    rw [hA, hB]
    exact hdifference
  · have hdifference : J (B,A) ≠ J (B,B) := by
      simpa only [hJ] using hrow
    apply physicalOriginalUnitReceiverFullLinkEnergy_pos_of_targetFiber_difference
      H beta hbeta B (split A).2 (split A).1 (split B).1
    change J (B, split.symm ((split A).1, (split A).2)) ≠
      J (B, split.symm ((split B).1, (split A).2))
    rw [hA, hB]
    exact hdifference

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
