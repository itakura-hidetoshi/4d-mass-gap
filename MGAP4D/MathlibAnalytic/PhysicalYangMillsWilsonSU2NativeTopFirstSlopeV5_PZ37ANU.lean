import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2NativeFirstHaarMomentTaylorV5_PZ37ANT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANU — true original physical top/first-Wilson-mode slope reduction

ANT gives the genuine native SU(2) first one-slab Wilson action insertion
moment, as a pair-Haar L² inner product. ANR controls replacement of the
actual positive normalized physical top eigenvector by the original Haar
constant at order beta².

This file combines those exact original-model facts into a bound on
  |<Omega_{H,beta},v1_H> + beta*m_H|
with positive denominator equal to the REAL actual Wilson top norm.
It preserves the exact original physical Hilbert, one-slab Wilson action,
spatial halfweights and crossing, the actual Haar first Gram--Schmidt
mode, and the original finite volume.

The moment m_H is a literal actual SU(2) pair-Haar first-action moment;
its value and nonvanishing are NOT assumed or proved in this stage.
The source gives an explicit conditional positive-beta nonvanishing test
as soon as that true moment can be bounded away from zero. No OS gluing
or uniform/continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANU_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANU_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANU_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANU_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANU_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANU_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37ANU_sliceHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  infer_instance

/-- Actual unchanged original SU(2) one-slab full Wilson action moment,
using the native finite-volume pair-Haar L² class, the genuine constant-one
physical Gauss-law state and the actual first spatial Wilson-energy
Gram--Schmidt mode, not a proxy tensor. -/
noncomputable def p4Q2PZ37ANU_originalFirstHaarActionMoment (H : ℕ) : ℝ :=
  inner ℝ
    (p4Q2PZ37ANT_originalSlabAction_pairHaarL2 H)
    (realL2ExternalTensor
      ((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
      ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
          PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
          Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)))

/-- Elementary scalar bridge; error in replacing the actual normalized
Wilson vacuum + true transfer norm, and error in the fixed-Haar
action insertion, both remain quadratic. The norm multiplier lambda
is retained rather than replaced by a guessed physical eigenvalue. -/
theorem p4Q2PZ37ANU_realScalar_topFirstSlope_weighted_error
    (lambda beta b response moment x : ℝ)
    (hlambda : 0 < lambda)
    (hbeta : 0 ≤ beta)
    (hVacuum :
      lambda * |lambda * b - response| ≤ 2 * x^2)
    (hMoment :
      |response + beta * moment| ≤ x^2)
    (hNormVariation : |lambda - 1| ≤ x) :
    lambda^2 * |b + beta * moment| ≤
      (2 + lambda) * x^2 +
        lambda * beta * |moment| * x := by
  have hlambda0 : 0 ≤ lambda := le_of_lt hlambda
  have hfirst :
      |lambda * (lambda * b - response)| ≤ 2 * x^2 := by
    simpa only [abs_mul, abs_of_nonneg hlambda0] using hVacuum
  have hsecond :
      |lambda * (response + beta * moment)| ≤ lambda * x^2 := by
    rw [abs_mul, abs_of_nonneg hlambda0]
    exact mul_le_mul_of_nonneg_left hMoment hlambda0
  have hthird :
      |(lambda * beta * moment) * (lambda - 1)| ≤
        (lambda * beta * |moment|) * x := by
    calc
      |(lambda * beta * moment) * (lambda - 1)| =
          (lambda * beta * |moment|) * |lambda - 1| := by
        simp only [abs_mul, abs_of_nonneg hlambda0,
          abs_of_nonneg hbeta]
      _ ≤ (lambda * beta * |moment|) * x :=
        mul_le_mul_of_nonneg_left hNormVariation
          (mul_nonneg (mul_nonneg hlambda0 hbeta) (abs_nonneg moment))
  have hidentity :
      lambda^2 * (b + beta * moment) =
        lambda * (lambda * b - response) +
          lambda * (response + beta * moment) +
          (lambda * beta * moment) * (lambda - 1) := by ring
  have htriangle :
      |lambda^2 * (b + beta * moment)| ≤
        |lambda * (lambda * b - response)| +
        |lambda * (response + beta * moment)| +
        |(lambda * beta * moment) * (lambda - 1)| := by
    rw [hidentity]
    calc
      |lambda * (lambda * b - response) +
          lambda * (response + beta * moment) +
          (lambda * beta * moment) * (lambda - 1)| ≤
          |lambda * (lambda * b - response) +
            lambda * (response + beta * moment)| +
          |(lambda * beta * moment) * (lambda - 1)| :=
        abs_add_le _ _
      _ ≤ (|lambda * (lambda * b - response)| +
          |lambda * (response + beta * moment)|) +
          |(lambda * beta * moment) * (lambda - 1)| :=
        by
          simpa only [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right
              (abs_add_le (lambda * (lambda * b - response))
                (lambda * (response + beta * moment)))
              |(lambda * beta * moment) * (lambda - 1)|)
  calc
    lambda^2 * |b + beta * moment| =
        |lambda^2 * (b + beta * moment)| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg lambda)]
    _ ≤ |lambda * (lambda * b - response)| +
          |lambda * (response + beta * moment)| +
          |(lambda * beta * moment) * (lambda - 1)| := htriangle
    _ ≤ 2 * x^2 + lambda * x^2 +
          (lambda * beta * |moment|) * x := by
        linarith [hfirst, hsecond, hthird]
    _ = (2 + lambda) * x^2 +
          lambda * beta * |moment| * x := by ring

/-- For all finite H and nonnegative beta with original action budget
C_H beta≤1, this is the genuinely original physical Wilson top/first-mode
first-order expansion with an explicit weighted quadratic error.
The coefficient is the actual pair-Haar first-action moment. -/
theorem p4Q2PZ37ANU_originalPhysicalTopFirstSlope_weightedError_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖)^2 *
      |inner ℝ
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
            H 2 (by norm_num) beta hbeta)
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) +
        beta * p4Q2PZ37ANU_originalFirstHaarActionMoment H| ≤
      (2 +
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta)^2 +
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
        beta * |p4Q2PZ37ANU_originalFirstHaarActionMoment H| *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let lambda : ℝ := ‖T‖
  let moment : ℝ := p4Q2PZ37ANU_originalFirstHaarActionMoment H
  let response : ℝ := inner ℝ ((T - U) c) v1
  let b : ℝ := inner ℝ Ω v1
  let x : ℝ := C * beta
  have hpos : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hVacuum : lambda * |lambda * b - response| ≤ 2 * x^2 :=
    p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_weightedError_le_quadratic
      H beta hbeta
  have hMoment : |response + beta * moment| ≤ x^2 :=
    p4Q2PZ37ANT_originalFixedHaarResponse_firstMoment_quadratic
      H beta hbeta hsmall
  have hNorm0 : ‖U‖ = 1 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one H
  have hNormVariation : |lambda - 1| ≤ x := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    rw [hNorm0] at h
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  exact p4Q2PZ37ANU_realScalar_topFirstSlope_weighted_error
    lambda beta b response moment x hpos hbeta hVacuum hMoment hNormVariation

/-- Divide the already-proved exact weighted Wilson first-order remainder
by the TRUE strictly positive original physical top transfer norm squared.
No unproven spectral equality or auxiliary normalization. -/
theorem p4Q2PZ37ANU_originalPhysicalTopFirstSlope_divTopNormSquared
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) +
      beta * p4Q2PZ37ANU_originalFirstHaarActionMoment H| ≤
      ((2 +
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta‖) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta)^2 +
       ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖ *
        beta * |p4Q2PZ37ANU_originalFirstHaarActionMoment H| *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta)) /
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖)^2 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let b := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta)
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  let m := p4Q2PZ37ANU_originalFirstHaarActionMoment H
  let x := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
    beta
  have hTpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hbound :
      ‖T‖^2 * |b + beta * m| ≤
        (2 + ‖T‖) * x^2 + ‖T‖ * beta * |m| * x :=
    p4Q2PZ37ANU_originalPhysicalTopFirstSlope_weightedError_le
      H beta hbeta hsmall
  apply (le_div_iff₀ (sq_pos_of_pos hTpos)).2
  calc
    |b + beta * m| * ‖T‖^2 =
        ‖T‖^2 * |b + beta * m| := mul_comm _ _
    _ ≤ _ := hbound

/-- Model-native SU(2) positive-coupling top/first-mode nonvanishing
criterion with an explicitly measured original Wilson first Haar action
moment. The moment's NONZERO VALUE IS NOT asserted by this criterion. -/
theorem p4Q2PZ37ANU_originalPhysicalTopFirstMode_nonzero_of_momentDominance
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1)
    (hdominance :
      (2 +
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta hbeta‖) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta)^2 +
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ *
        beta * |p4Q2PZ37ANU_originalFirstHaarActionMoment H| *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
          beta) <
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖)^2 *
        beta * |p4Q2PZ37ANU_originalFirstHaarActionMoment H|) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≠ 0 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let b := inner ℝ
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) beta hbeta)
    (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)
  let m := p4Q2PZ37ANU_originalFirstHaarActionMoment H
  let x := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
    beta
  have hbound :
      ‖T‖^2 * |b + beta * m| ≤
        (2 + ‖T‖) * x^2 + ‖T‖ * beta * |m| * x :=
    p4Q2PZ37ANU_originalPhysicalTopFirstSlope_weightedError_le
      H beta hbeta hsmall
  intro hzero
  have hbzero : b = 0 := hzero
  have hz : ‖T‖^2 * |b + beta * m| =
      ‖T‖^2 * beta * |m| := by
    rw [hbzero, zero_add, abs_mul, abs_of_nonneg hbeta]
    ring
  exact (not_lt_of_ge (hz ▸ hbound)) hdominance

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANU_originalFirstHaarActionMoment
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANU_realScalar_topFirstSlope_weighted_error
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANU_originalPhysicalTopFirstSlope_weightedError_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANU_originalPhysicalTopFirstSlope_divTopNormSquared
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANU_originalPhysicalTopFirstMode_nonzero_of_momentDominance
