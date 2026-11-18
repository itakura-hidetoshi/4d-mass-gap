import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2VacuumStabilityFixedSourceResponseV5_PZ37ANR
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryOneSlabTransferRawIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANS — exact original Wilson kernel first variation and fixed-Haar response

The actual SU(2) one-slab Wilson kernel has the exact beta=0 derivative
  dK/dβ|0 (A,B) = -S_original(A,B).
Its true finite-volume action S is bounded by C_H, yielding the explicit
quadratic Taylor remainder for C_H β <= 1. No alternate Wilson model or
proxy kernel is introduced.

The ACTUAL fixed-Haar response r_H(β)=< (T_β - T_0) c,v1_H> is the original
two-boundary Haar integral of the original Wilson kernel against the true
constant physical Gauss-law state and true first Gram--Schmidt Wilson mode.
The ANR O(beta^2) bound gives precise finite-beta (and small-beta) criteria
for NONZERO top-v1 overlap when the concrete response is large enough.

These criteria are conditional; the exact two-boundary action-insertion
moment and its sign/nonvanishing require a further independent proof.
No completed OS boundary operator equivalence, volume-uniform mass gap,
or continuum 4D Yang--Mills claim is made.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANS_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANS_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANS_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANS_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANS_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANS_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For the unchanged, genuine original SU(2) Wilson one-slab kernel,
the parameter derivative at zero equals minus the FULL original symmetric
slab action, including both spatial half-weights and crossing. -/
theorem p4Q2PZ37ANS_originalOneSlabKernel_hasDerivAt_betaZero
    (H : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    HasDerivAt
      (fun beta : ℝ =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta A B)
      (-periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
        H 2 A B) 0 := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_hasDerivAt_beta
      H 2 0 A B
  simpa only
    [p4Q2PZ37ANO_originalOneSlabKernel_betaZero H A B, mul_one]
    using h

/-- Pointwise second-order Taylor bound for the *actual original one-slab
Wilson kernel*, not an independently normalized surrogate. Valid for every
finite H and beta>=0 when the total original slab action budget obeys
C_H beta <= 1. The inserted first-order action is exactly the full
spatial-halfweight/crossing original Wilson action. -/
theorem p4Q2PZ37ANS_originalOneSlabKernel_quadraticRemainder
    (H : ℕ) (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤ 1)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) :
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B - 1 +
      beta * periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
        H 2 A B| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)^2 := by
  let S := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2 A B
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hS0 : 0 ≤ S :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) A B
  have hSC : S ≤ C :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
      H 2 (by norm_num) A B
  have hprod0 : 0 ≤ beta * S := mul_nonneg hbeta hS0
  have hprodC : beta * S ≤ C * beta := by
    calc
      beta * S ≤ beta * C := mul_le_mul_of_nonneg_left hSC hbeta
      _ = C * beta := mul_comm _ _
  have habs : |-(beta * S)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hprod0]
    exact hprodC.trans hsmall
  have hTaylor :=
    Real.abs_exp_sub_one_sub_id_le (x := -(beta * S)) habs
  calc
    |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H 2 beta A B - 1 + beta *
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
            H 2 A B| =
      |Real.exp (-(beta * S)) - 1 - (-(beta * S))| := by
        rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
        dsimp [S]
        ring
    _ ≤ (-(beta * S))^2 := hTaylor
    _ = (beta * S)^2 := by ring
    _ ≤ (C * beta)^2 := by
      nlinarith [sq_nonneg (C * beta - beta * S)]

/-- The genuine zero-Haar-vacuum to first Wilson-mode transfer response is
LITERALLY the native two-boundary original Wilson kernel Haar integral.
The beta-zero rank-one reference subtraction vanishes because the original
first spatial Wilson Gram--Schmidt mode is Haar-centered. -/
theorem p4Q2PZ37ANS_originalFixedHaarResponse_eq_nativeKernelHaarIntegral
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    inner ℝ
      ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) =
      ∫ p : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H 2 beta p.1 p.2 *
          (((periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
              Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
            p.1 *
          ((p4Q2PZ37AMU_actualPhysicalGaussMode H 1 :
              PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
              Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2))
            p.2)
        ∂(periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2) := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have hUzero : inner ℝ (U c) v1 = 0 :=
    p4Q2PZ37ANP_originalPhysicalBetaZero_allInput_modeOne_inner_zero H c
  have hraw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_inner_eq_rawIntegral
      H 2 (by norm_num) beta hbeta c v1
  calc
    inner ℝ ((T - U) c) v1 =
        inner ℝ (T c) v1 - inner ℝ (U c) v1 := by
          rw [ContinuousLinearMap.sub_apply, inner_sub_left]
    _ = inner ℝ (T c) v1 := by rw [hUzero, sub_zero]
    _ = _ := hraw

/-- If the exactly observed fixed-Haar Wilson response dominates the
certified quadratic vacuum-replacement error, the true native physical
top/first-mode overlap MUST be nonzero. The premise is an explicit
test on the original one-slab physical operator, not an assumed
OS-boundary representation or continuum gap. -/
theorem p4Q2PZ37ANS_originalPhysicalTopModeOne_nonzero_of_response_gt_quadratic
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hresponse :
      2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)^2 <
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta hbeta‖ *
        |inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) beta hbeta -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) 0 (by norm_num))
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)|) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≠ 0 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H 2 (by norm_num) beta hbeta
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have herror :
      ‖T‖ * |‖T‖ * inner ℝ Ω v1 - inner ℝ ((T - U) c) v1| ≤
        2 * (C * beta)^2 :=
    p4Q2PZ37ANR_originalTopFirstMode_fixedHaarResponse_weightedError_le_quadratic
      H beta hbeta
  intro hzero
  have hzeroScale : ‖T‖ * inner ℝ Ω v1 = 0 := by rw [hzero, mul_zero]
  rw [hzeroScale, zero_sub, abs_neg] at herror
  exact (not_lt_of_ge herror) hresponse

/-- Eliminating the unknown true top-transfer norm from the previous
nonzero response condition when 0 <= C_H beta < 1. This is STILL a
conditional finite-volume original-Wilson criterion; the fixed-Haar
response must be independently evaluated in the native model. -/
theorem p4Q2PZ37ANS_originalPhysicalTopModeOne_nonzero_of_explicitSmallBeta_response
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta < 1)
    (hresponse :
      2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta)^2 <
      (1 - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) *
        |inner ℝ
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) beta hbeta -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) 0 (by norm_num))
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
          (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)|) :
    inner ℝ
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) beta hbeta)
      (p4Q2PZ37AMU_actualPhysicalGaussMode H 1) ≠ 0 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let c : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hnormLower : 1 - C * beta ≤ ‖T‖ :=
    p4Q2PZ37ANQ_originalPhysicalTopNorm_ge_one_sub_budgetBeta H beta hbeta
  have habs : 0 ≤ |inner ℝ ((T - U) c) v1| := abs_nonneg _
  have hstrict :
      2 * (C * beta)^2 < ‖T‖ * |inner ℝ ((T - U) c) v1| :=
    lt_of_lt_of_le hresponse
      (mul_le_mul_of_nonneg_right hnormLower habs)
  exact
    p4Q2PZ37ANS_originalPhysicalTopModeOne_nonzero_of_response_gt_quadratic
      H beta hbeta hstrict

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANS_originalOneSlabKernel_hasDerivAt_betaZero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANS_originalOneSlabKernel_quadraticRemainder
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANS_originalFixedHaarResponse_eq_nativeKernelHaarIntegral
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANS_originalPhysicalTopModeOne_nonzero_of_response_gt_quadratic
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANS_originalPhysicalTopModeOne_nonzero_of_explicitSmallBeta_response
