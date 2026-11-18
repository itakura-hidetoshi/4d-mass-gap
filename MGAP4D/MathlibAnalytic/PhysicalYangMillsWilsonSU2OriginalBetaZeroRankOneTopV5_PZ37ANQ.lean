import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2VacuumFirstModeBetaLipschitzV5_PZ37ANP
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ANQ — exact beta-zero physical Wilson rank-one operator and vacuum

The ACTUAL compact physical SU(2) Wilson one-slab transfer, restricted to
the original Gauss-law Hilbert carrier, equals the rank-one orthogonal
projection onto the literal spatial Haar constant at beta=0, for every H.
This follows from the exact original ANO constant product-Haar L² kernel,
the unchanged Gauss restriction, and the exact real L² separable pairing.

The unmodified original top eigenvalue at beta zero is precisely one, and
the *chosen nonnegative normalized physical top eigenvector* is exactly the
same genuine Haar constant unit vector (not just an abstract top eigenspace).
The fixed-volume beta-Lipschitz perturbation then controls the top norm from
below for all beta >= 0; if C_H beta < 1 it gives a completely explicit
bound on the first Wilson-mode overlap with no unknown top-norm denominator.

No assertion of first-mode nonvanishing at beta>0, no top derivative,
positive-time OS equivalence, volume-uniform gap or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000

local instance p4Q2PZ37ANQ_group :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ANQ_compact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ANQ_countable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ANQ_measurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ANQ_borel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ANQ_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p4Q2PZ37ANQ_spatialHaarSFinite (H : ℕ) :
    SFinite (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2) := by
  infer_instance

/-- The exact original physical SU(2) beta-zero transfer is the RANK-ONE
orthogonal projection onto the actual Haar constant Gauss-law state.
This is proved for every physical input by equality of all native
physical Hilbert matrix coefficients, not by identification with an OS
boundary operator or use of an abstract rank-one proxy. -/
theorem p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_eq_haarRankOne
    (H : ℕ)
    (f : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) 0 (by norm_num) f =
      (inner ℝ (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)
          f) •
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
  let c : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  let v0 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  apply ext_inner_right ℝ
  intro g
  calc
    inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) 0 (by norm_num) f) g =
      realL2HilbertSchmidtKernelPairing
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
          H 2 (by norm_num) 0 (by norm_num))
        (f : Lp ℝ 2 μ) (g : Lp ℝ 2 μ) := by
          change
            inner ℝ
              (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
                H 2 (by norm_num) 0 (by norm_num) (f : Lp ℝ 2 μ))
              (g : Lp ℝ 2 μ) = _
          exact periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
            H 2 (by norm_num) 0 (by norm_num) f g
    _ = inner ℝ c (f : Lp ℝ 2 μ) * inner ℝ c (g : Lp ℝ 2 μ) := by
          rw [p4Q2PZ37ANO_originalOneSlabPairKernel_betaZero_eq_oneTensor]
          exact realL2HilbertSchmidtKernelPairing_externalTensor
            c (f : Lp ℝ 2 μ) c (g : Lp ℝ 2 μ)
    _ = inner ℝ v0 f * inner ℝ v0 g := rfl
    _ = inner ℝ ((inner ℝ v0 f) • v0) g := by
          exact (real_inner_smul_left v0 g (inner ℝ v0 f)).symm

/-- The physical original one-slab transfer at beta=0 has operator norm
exactly 1. This is NOT merely a chosen normalization convention: it is
deduced from the native Haar rank-one formula and ‖constant‖=1. -/
theorem p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one
    (H : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) 0 (by norm_num)‖ = 1 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let v0 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hv0 : ‖v0‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hself : inner ℝ v0 v0 = 1 := by
    rw [real_inner_self_eq_norm_sq, hv0]
    norm_num
  have hvfix : T v0 = v0 := by
    rw [p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_eq_haarRankOne H v0]
    rw [hself, one_smul]
  have hupper : ‖T‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound T (by norm_num)
    intro f
    calc
      ‖T f‖ = ‖(inner ℝ v0 f) • v0‖ := by
        rw [p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_eq_haarRankOne]
      _ = |inner ℝ v0 f| * ‖v0‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = |inner ℝ v0 f| := by rw [hv0, mul_one]
      _ ≤ ‖v0‖ * ‖f‖ := abs_real_inner_le_norm v0 f
      _ = 1 * ‖f‖ := by rw [hv0]
  have hlower : 1 ≤ ‖T‖ := by
    have h := T.le_opNorm v0
    rw [hvfix, hv0, mul_one] at h
    exact h
  exact le_antisymm hupper hlower

/-- The ACTUAL canonical nonnegative physical Wilson top vector at zero
coupling is the original Gauss-law Haar constant-one state, for EVERY H.
No eigenvector-choice continuity or positive-coupling uniqueness is assumed. -/
theorem p4Q2PZ37ANQ_originalPhysicalBetaZero_top_eq_haarConstant
    (H : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
        H 2 (by norm_num) 0 (by norm_num) =
      periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2 := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let Ω : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
      H 2 (by norm_num) 0 (by norm_num)
  let v0 : PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H 2 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  have hNormT : ‖T‖ = 1 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one H
  have hNormΩ : ‖Ω‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) 0 (by norm_num)
  have hv0 : ‖v0‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hEigen : T Ω = ‖T‖ • Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) 0 (by norm_num)
  have hFixed : T Ω = Ω := by
    rw [hEigen, hNormT, one_smul]
  have hRank : T Ω = (inner ℝ v0 Ω) • v0 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_eq_haarRankOne H Ω
  have hPositive : 0 < inner ℝ Ω v0 := by
    have h := p4Q2PZ37ANM_originalPhysicalTop_inner_modeZero_pos
      H 0 (by norm_num)
    rw [p4Q2PZ37ANM_actualModeZero_eq_physicalConstant] at h
    exact h
  have haPositive : 0 < inner ℝ v0 Ω := by
    calc
      0 < inner ℝ Ω v0 := hPositive
      _ = inner ℝ v0 Ω := real_inner_comm _ _
  have hNormScale : ‖(inner ℝ v0 Ω) • v0‖ = 1 := by
    rw [← hRank, hFixed]
    exact hNormΩ
  have haOne : inner ℝ v0 Ω = 1 := by
    rw [norm_smul, Real.norm_eq_abs, hv0, mul_one,
      abs_of_pos haPositive] at hNormScale
    exact hNormScale
  calc
    Ω = T Ω := hFixed.symm
    _ = (inner ℝ v0 Ω) • v0 := hRank
    _ = v0 := by rw [haOne, one_smul]

/-- With the exact original beta-zero norm=1 and the already-certified
physical one-slab beta-Lipschitz norm bound, the original physical top
eigenvalue obeys an EXPLICIT lower bound for every finite H and beta>=0. -/
theorem p4Q2PZ37ANQ_originalPhysicalTopNorm_ge_one_sub_budgetBeta
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    1 - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta‖ := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let U := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) 0 (by norm_num)
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hUnorm : ‖U‖ = 1 :=
    p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one H
  have hLip : |‖T‖ - 1| ≤ C * beta := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H 2 (by norm_num) 0 beta (by norm_num) hbeta
    rw [hUnorm] at h
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbeta] using h
  have hsub : 1 - ‖T‖ ≤ C * beta := by
    calc
      1 - ‖T‖ ≤ |1 - ‖T‖| := le_abs_self _
      _ = |‖T‖ - 1| := by rw [abs_sub_comm]
      _ ≤ C * beta := hLip
  dsimp [T, C] at hsub ⊢
  linarith

/-- For beta·globalActionBudget(H)<1 the EXACT native SU(2) Wilson vacuum
first-mode overlap is bounded with NO UNKNOWN top-norm denominator.
The estimate is volume-dependent and has no sign/nonzero conclusion. -/
theorem p4Q2PZ37ANQ_originalPhysicalTopModeOne_explicitSmallBeta_bound
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta < 1) :
    |inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
          H 2 (by norm_num) beta hbeta)
        (p4Q2PZ37AMU_actualPhysicalGaussMode H 1)| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) /
      (1 - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        beta) := by
  let C := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta hbeta
  let Ω := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector
    H 2 (by norm_num) beta hbeta
  let v1 := p4Q2PZ37AMU_actualPhysicalGaussMode H 1
  have hnormpos : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hdelta : 0 < 1 - C * beta := sub_pos.mpr hsmall
  have hnum : 0 ≤ C * beta :=
    mul_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H)
      hbeta
  have hlower : 1 - C * beta ≤ ‖T‖ :=
    p4Q2PZ37ANQ_originalPhysicalTopNorm_ge_one_sub_budgetBeta H beta hbeta
  have hANP :
      |inner ℝ Ω v1| ≤ C * beta / ‖T‖ :=
    p4Q2PZ37ANP_originalPhysicalTopModeOne_abs_le_budgetBeta_div_topNorm
      H beta hbeta
  calc
    |inner ℝ Ω v1| ≤ C * beta / ‖T‖ := hANP
    _ ≤ C * beta / (1 - C * beta) := by
        apply (div_le_div_iff₀ hnormpos hdelta).2
        exact mul_le_mul_of_nonneg_left hlower hnum

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_eq_haarRankOne
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANQ_originalPhysicalBetaZero_transfer_norm_eq_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANQ_originalPhysicalBetaZero_top_eq_haarConstant
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANQ_originalPhysicalTopNorm_ge_one_sub_budgetBeta
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ANQ_originalPhysicalTopModeOne_explicitSmallBeta_bound
