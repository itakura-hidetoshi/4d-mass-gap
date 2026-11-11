import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalThirdPowerHaarCauchyFloorV5_PZ37AKB
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKC — original Wilson all-positive-powers Haar-Cauchy floor

AKB certified the actual third-power lower bound B³/V² ≤ ‖S³ f₀‖².
This new leaf treats ALL natural n≥1 without selecting an arbitrary
cutoff. For a symmetric real-Hilbert operator S, squared-norm moments
aₙ := ‖Sⁿ x‖² are log-convex:
  aₙ₊₁² ≤ aₙ aₙ₊₂.
If a₀>0 and a₁>0, positivity and monotone successive ratios yield
  a₁ⁿ⁺¹ ≤ a₀ⁿ aₙ₊₁.
Using the unchanged real physical Wilson transfer S, the unchanged
original centered ZW source f₀, V=‖f₀‖²>0, and the genuine Haar
AJA certificate 0<B≤‖S f₀‖² proves at each finite H, beta>0:
  0 < Bⁿ⁺¹/Vⁿ ≤ ‖Sⁿ⁺¹ f₀‖²    (all n : ℕ).
This is only a pointwise positive lower floor; it supplies no
volume-uniform gap, no strict AJA power witness, and no top rank-one
claim. Original Wilson/Haar/ZW/AJA definitions and pins are untouched.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Every log-convex real sequence with positive first two entries
has strictly positive subsequent entries and nondecreasing successive
ratios after cross multiplication. No positive upper bound is used. -/
theorem real_positive_logConvex_sequence_ratio_akc
    (a : ℕ → ℝ) (hZero : 0 < a 0) (hOne : 0 < a 1)
    (hLog : ∀ n : ℕ, (a (n + 1)) ^ 2 ≤ a n * a (n + 1 + 1)) :
    ∀ n : ℕ, 0 < a n ∧ 0 < a (n + 1) ∧
      a n * a 1 ≤ a (n + 1) * a 0 := by
  intro n
  induction n with
  | zero =>
      exact ⟨hZero, hOne, le_of_eq (mul_comm (a 0) (a 1))⟩
  | succ n ih =>
      rcases ih with ⟨hN, hNext, hRatio⟩
      have hNextNext : 0 < a (n + 1 + 1) := by
        by_contra hNot
        have hLe : a (n + 1 + 1) ≤ 0 := le_of_not_gt hNot
        have hProd : a n * a (n + 1 + 1) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos hN.le hLe
        have hSq : 0 < (a (n + 1)) ^ 2 := pow_pos hNext 2
        linarith only [hLog n, hProd, hSq]
      have hMult :
          a n * (a (n + 1) * a 1) ≤
          a n * (a (n + 1 + 1) * a 0) := by
        calc
          a n * (a (n + 1) * a 1) =
              (a n * a 1) * a (n + 1) := by ring
          _ ≤ (a (n + 1) * a 0) * a (n + 1) :=
            mul_le_mul_of_nonneg_right hRatio hNext.le
          _ = (a (n + 1)) ^ 2 * a 0 := by ring
          _ ≤ (a n * a (n + 1 + 1)) * a 0 :=
            mul_le_mul_of_nonneg_right (hLog n) hZero.le
          _ = a n * (a (n + 1 + 1) * a 0) := by ring
      have hRatioNext :
          a (n + 1) * a 1 ≤ a (n + 1 + 1) * a 0 :=
        (mul_le_mul_iff_of_pos_left hN).mp hMult
      simpa only [Nat.succ_eq_add_one] using
        (show 0 < a (n + 1) ∧ 0 < a (n + 1 + 1) ∧
          a (n + 1) * a 1 ≤ a (n + 1 + 1) * a 0 from
          ⟨hNext, hNextNext, hRatioNext⟩)

/-- Log-convexity and positive initial terms imply the exact arbitrary
positive-power lower bound without an operator norm or spectral gap. -/
theorem real_positive_logConvex_sequence_powerFloor_akc
    (a : ℕ → ℝ) (hZero : 0 < a 0) (hOne : 0 < a 1)
    (hLog : ∀ n : ℕ, (a (n + 1)) ^ 2 ≤ a n * a (n + 1 + 1)) :
    ∀ n : ℕ, (a 1) ^ (n + 1) ≤ (a 0) ^ n * a (n + 1) := by
  have hRatio := real_positive_logConvex_sequence_ratio_akc a hZero hOne hLog
  intro n
  induction n with
  | zero =>
      simpa using (le_refl (a 1))
  | succ n ih =>
      have hR : a (n + 1) * a 1 ≤ a (n + 1 + 1) * a 0 :=
        (hRatio (n + 1)).2.2
      change (a 1) ^ ((n + 1) + 1) ≤
        (a 0) ^ (n + 1) * a (n + 1 + 1)
      calc
        (a 1) ^ ((n + 1) + 1) = (a 1) ^ (n + 1) * a 1 := by
          rw [pow_succ]
        _ ≤ ((a 0) ^ n * a (n + 1)) * a 1 :=
          mul_le_mul_of_nonneg_right ih hOne.le
        _ = (a 0) ^ n * (a (n + 1) * a 1) := by ring
        _ ≤ (a 0) ^ n * (a (n + 1 + 1) * a 0) :=
          mul_le_mul_of_nonneg_left hR (pow_nonneg hZero.le n)
        _ = (a 0) ^ (n + 1) * a (n + 1 + 1) := by
          rw [pow_succ]
          ring

/-- The actual symmetric real-Hilbert power moments are log-convex
at every shift: adjacent Wilson powers require no top rank assumption. -/
theorem realHilbert_symmetric_power_normSq_logConvex_akc
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) (n : ℕ) :
    (‖(S ^ (n + 1)) x‖ ^ 2) ^ 2 ≤
      ‖(S ^ n) x‖ ^ 2 * ‖(S ^ (n + 2)) x‖ ^ 2 := by
  have hOne : (S ^ (n + 1)) x = S ((S ^ n) x) := by
    rw [show n + 1 = 1 + n by omega, pow_add, pow_one]
    rfl
  have hTwo : (S ^ (n + 2)) x = (S ^ 2) ((S ^ n) x) := by
    rw [show n + 2 = 2 + n by omega, pow_add]
    rfl
  have hCS :=
    realHilbert_symmetric_secondPower_normSq_Cauchy_aka
      S hSymm ((S ^ n) x)
  calc
    (‖(S ^ (n + 1)) x‖ ^ 2) ^ 2 =
        (‖S ((S ^ n) x)‖ ^ 2) ^ 2 := by rw [hOne]
    _ ≤ ‖(S ^ n) x‖ ^ 2 * ‖(S ^ 2) ((S ^ n) x)‖ ^ 2 := hCS
    _ = ‖(S ^ n) x‖ ^ 2 * ‖(S ^ (n + 2)) x‖ ^ 2 := by rw [hTwo]

local notation "GC" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKC_group : IsTopologicalGroup GC :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKC_compact : CompactSpace GC :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKC_secondCountable : SecondCountableTopology GC :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKC_measurable : MeasurableSpace GC :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKC_borel : BorelSpace GC :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKC_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "PhysC" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgC" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muC" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fC" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SC" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "VC" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "uC" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mC" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AKC_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- Exact original Wilson positive-power energy floor for EVERY exponent.
The original SU(2) physical operator, genuine ZW source and Haar-AJA
certificate are used verbatim; the bound is only pointwise in H,beta. -/
theorem p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_mul
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ((mC beta hbeta.le) ^ 2 *
      Measure.real muC
        {U : CfgC | uC beta hbeta.le U < -(mC beta hbeta.le)}) ^ (n + 1) ≤
      VC ^ n * ‖((SC beta hbeta.le) ^ (n + 1)) fC‖ ^ 2 := by
  let S : PhysC →L[ℝ] PhysC := SC beta hbeta.le
  let B : ℝ :=
    (mC beta hbeta.le) ^ 2 *
      Measure.real muC
        {U : CfgC | uC beta hbeta.le U < -(mC beta hbeta.le)}
  let a : ℕ → ℝ := fun k => ‖(S ^ k) fC‖ ^ 2
  have hSymm : (S : PhysC →ₗ[ℝ] PhysC).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hBA : B ≤ ‖S fC‖ ^ 2 :=
    p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta
  have hBpos : 0 < B :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hV : 0 < VC :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hVariance : ‖fC‖ ^ 2 = VC :=
    p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H
  have hA0 : 0 < a 0 := by
    simpa [a, hVariance] using hV
  have hA1 : 0 < a 1 := by
    simpa [a] using hBpos.trans_le hBA
  have hLog : ∀ k : ℕ,
      (a (k + 1)) ^ 2 ≤ a k * a (k + 1 + 1) := by
    intro k
    simpa only [a, show k + 1 + 1 = k + 2 by omega] using
      (realHilbert_symmetric_power_normSq_logConvex_akc S hSymm fC k)
  have hPower :=
    real_positive_logConvex_sequence_powerFloor_akc a hA0 hA1 hLog n
  have hPower' :
      (‖S fC‖ ^ 2) ^ (n + 1) ≤
        VC ^ n * ‖(S ^ (n + 1)) fC‖ ^ 2 := by
    calc
      (‖S fC‖ ^ 2) ^ (n + 1) = (a 1) ^ (n + 1) := by simp [a]
      _ ≤ (a 0) ^ n * a (n + 1) := hPower
      _ = VC ^ n * ‖(S ^ (n + 1)) fC‖ ^ 2 := by simp [a, hVariance]
  exact (pow_le_pow_left₀ hBpos.le hBA (n + 1)).trans hPower'

/-- Genuine unconditional normalized Haar-Cauchy floor for every n+1>0.
No H-uniform lower bound is asserted. -/
theorem p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_div
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (((mC beta hbeta.le) ^ 2 *
      Measure.real muC
        {U : CfgC | uC beta hbeta.le U < -(mC beta hbeta.le)}) ^ (n + 1)) /
      VC ^ n ≤ ‖((SC beta hbeta.le) ^ (n + 1)) fC‖ ^ 2 := by
  have hV : 0 < VC :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hFloor :=
    p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_mul H beta hbeta n
  apply (div_le_iff₀ (pow_pos hV n)).2
  nlinarith only [hFloor]

/-- No positive power of the original finite-H Wilson transfer annihilates
the centered genuine ZW source at any positive coupling. -/
theorem p4Q2PZ37AKC_originalAllPositivePowers_energy_pos
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    0 < ‖((SC beta hbeta.le) ^ (n + 1)) fC‖ ^ 2 := by
  have hV : 0 < VC :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hB :
      0 < (mC beta hbeta.le) ^ 2 *
        Measure.real muC
          {U : CfgC | uC beta hbeta.le U < -(mC beta hbeta.le)} :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hFloor :=
    p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_div H beta hbeta n
  have hPos :
      0 <
      (((mC beta hbeta.le) ^ 2 *
        Measure.real muC
          {U : CfgC | uC beta hbeta.le U < -(mC beta hbeta.le)}) ^ (n + 1)) /
        VC ^ n :=
    div_pos (pow_pos hB (n + 1)) (pow_pos hV n)
  exact hPos.trans_le hFloor

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Six new kernel-checked declarations, six independent axiom audits. -/
#print axioms MGAP4D.MathlibAnalytic.real_positive_logConvex_sequence_ratio_akc
#print axioms MGAP4D.MathlibAnalytic.real_positive_logConvex_sequence_powerFloor_akc
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_power_normSq_logConvex_akc
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKC_originalAllPositivePowers_HaarFloor_div
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKC_originalAllPositivePowers_energy_pos
