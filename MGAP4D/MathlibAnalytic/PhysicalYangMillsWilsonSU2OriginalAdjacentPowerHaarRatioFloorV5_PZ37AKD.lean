import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllPositivePowersHaarCauchyFloorV5_PZ37AKC
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKD — original Wilson adjacent-power Haar retention ratio

AKC proves a strictly positive lower bound on every genuine Wilson power.
Its exact log-convex ratio lemma also yields a stronger *local* statement:
for the ACTUAL centered source orbit aₙ=‖Sⁿ f₀‖², with the unchanged
Haar certificate 0<B≤a₁ and V=a₀>0, at each finite H, beta>0,

    B * aₙ ≤ V * aₙ₊₁,
    B / V ≤ aₙ₊₁ / aₙ       (all n : ℕ).

Consequently a putative geometric one-step factor q satisfying q*V<B
cannot upper bound aₙ₊₁ by q*aₙ at ANY n. These are source-orbit
retention inequalities, not spectral-gap or volume-uniform estimates.
The original physical Wilson/Haar/ZW/AJA quantities and assumptions are
never replaced, normalized differently, or weakened. No mass gap, top
rank-one property, or strict original AJA power witness follows.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A genuinely positive log-convex sequence, with original first-step
certificate B≤a₁, retains at least B/a₀ of its energy at each step. -/
theorem real_positive_logConvex_sequence_margin_step_akd
    (a : ℕ → ℝ) (B : ℝ)
    (hZero : 0 < a 0) (hB : 0 < B) (hBA : B ≤ a 1)
    (hLog : ∀ n : ℕ, (a (n + 1)) ^ 2 ≤ a n * a (n + 1 + 1))
    (n : ℕ) :
    B * a n ≤ a 0 * a (n + 1) := by
  have hOne : 0 < a 1 := hB.trans_le hBA
  obtain ⟨hN, _, hRatio⟩ :=
    real_positive_logConvex_sequence_ratio_akc a hZero hOne hLog n
  calc
    B * a n = a n * B := by ring
    _ ≤ a n * a 1 := mul_le_mul_of_nonneg_left hBA hN.le
    _ ≤ a (n + 1) * a 0 := hRatio
    _ = a 0 * a (n + 1) := by ring

/-- The lower retention ratio is meaningful since every denominator is
strictly positive; no rate or operator-norm hypothesis is smuggled in. -/
theorem real_positive_logConvex_sequence_margin_ratio_akd
    (a : ℕ → ℝ) (B : ℝ)
    (hZero : 0 < a 0) (hB : 0 < B) (hBA : B ≤ a 1)
    (hLog : ∀ n : ℕ, (a (n + 1)) ^ 2 ≤ a n * a (n + 1 + 1))
    (n : ℕ) :
    B / a 0 ≤ a (n + 1) / a n := by
  have hOne : 0 < a 1 := hB.trans_le hBA
  have hN : 0 < a n :=
    (real_positive_logConvex_sequence_ratio_akc a hZero hOne hLog n).1
  have hStep :=
    real_positive_logConvex_sequence_margin_step_akd a B hZero hB hBA hLog n
  apply (div_le_div_iff₀ hZero hN).2
  calc
    B * a n ≤ a 0 * a (n + 1) := hStep
    _ = a (n + 1) * a 0 := by ring

/-- Obstruction to an alleged subcritical stepwise upper rate q, with
q*a₀<B. This uses positivity of the actual orbit and a strict inequality. -/
theorem real_positive_logConvex_sequence_no_subcritical_step_akd
    (a : ℕ → ℝ) (B q : ℝ)
    (hZero : 0 < a 0) (hB : 0 < B) (hBA : B ≤ a 1)
    (hLog : ∀ n : ℕ, (a (n + 1)) ^ 2 ≤ a n * a (n + 1 + 1))
    (hQ : q * a 0 < B) (n : ℕ) :
    ¬ a (n + 1) ≤ q * a n := by
  intro hUpper
  have hOne : 0 < a 1 := hB.trans_le hBA
  have hN : 0 < a n :=
    (real_positive_logConvex_sequence_ratio_akc a hZero hOne hLog n).1
  have hStep :=
    real_positive_logConvex_sequence_margin_step_akd a B hZero hB hBA hLog n
  have hUpperMul : a 0 * a (n + 1) ≤ a 0 * (q * a n) :=
    mul_le_mul_of_nonneg_left hUpper hZero.le
  have hStrict : a 0 * (q * a n) < B * a n := by
    calc
      a 0 * (q * a n) = (q * a 0) * a n := by ring
      _ < B * a n := mul_lt_mul_of_pos_right hQ hN
  exact (lt_irrefl (B * a n))
    (lt_of_le_of_lt (hStep.trans hUpperMul) hStrict)

local notation "GD" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKD_group : IsTopologicalGroup GD :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKD_compact : CompactSpace GD :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKD_secondCountable : SecondCountableTopology GD :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKD_measurable : MeasurableSpace GD :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKD_borel : BorelSpace GD :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKD_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysD" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgD" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muD" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fD" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SD" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "VD" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "uD" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mD" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AKD_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- Positivity holds even at power zero: the genuine source has V>0.
For positive powers this is precisely the AKC kernel-checked fact. -/
theorem p4Q2PZ37AKD_originalAllPowers_energy_pos
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    0 < ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 := by
  cases n with
  | zero =>
      have hV : 0 < VD :=
        (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
      have hVariance : ‖fD‖ ^ 2 = VD :=
        p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H
      have hSource : 0 < ‖fD‖ ^ 2 := by
        rw [hVariance]
        exact hV
      simpa using hSource
  | succ k =>
      simpa only [Nat.succ_eq_add_one] using
        (p4Q2PZ37AKC_originalAllPositivePowers_energy_pos H beta hbeta k)

/-- ORIGINAL normalized Wilson transfer: genuine Haar certificate B
controls the actual adjacent source energy moments uniformly over
all natural powers at fixed finite H and positive beta. -/
theorem p4Q2PZ37AKD_originalAllPowers_HaarMargin_mul_energy_le_variance_next
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    ((mD beta hbeta.le) ^ 2 *
      Measure.real muD
        {U : CfgD | uD beta hbeta.le U < -(mD beta hbeta.le)}) *
      ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 ≤
    VD * ‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2 := by
  let S : PhysD →L[ℝ] PhysD := SD beta hbeta.le
  let B : ℝ :=
    (mD beta hbeta.le) ^ 2 *
      Measure.real muD
        {U : CfgD | uD beta hbeta.le U < -(mD beta hbeta.le)}
  let a : ℕ → ℝ := fun k => ‖(S ^ k) fD‖ ^ 2
  have hSymm : (S : PhysD →ₗ[ℝ] PhysD).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hBA : B ≤ ‖S fD‖ ^ 2 :=
    p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta
  have hBpos : 0 < B :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hV : 0 < VD :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hVariance : ‖fD‖ ^ 2 = VD :=
    p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H
  have hA0Eq : a 0 = VD := by
    calc
      a 0 = ‖fD‖ ^ 2 := by simp [a]
      _ = VD := hVariance
  have hA0 : 0 < a 0 := by
    rw [hA0Eq]
    exact hV
  have hBA' : B ≤ a 1 := by
    simpa [a] using hBA
  have hLog : ∀ k : ℕ,
      (a (k + 1)) ^ 2 ≤ a k * a (k + 1 + 1) := by
    intro k
    simpa only [a, show k + 1 + 1 = k + 2 by omega] using
      (realHilbert_symmetric_power_normSq_logConvex_akc S hSymm fD k)
  have hStep :=
    real_positive_logConvex_sequence_margin_step_akd
      a B hA0 hBpos hBA' hLog n
  change B * a n ≤ VD * a (n + 1)
  calc
    B * a n ≤ a 0 * a (n + 1) := hStep
    _ = VD * a (n + 1) := by rw [hA0Eq]

/-- Genuine finite-H pointwise lower bound for the ratio of successive
positive Wilson powers: B/V≤aₙ₊₁/aₙ, with no zero denominators. -/
theorem p4Q2PZ37AKD_originalAllPowers_HaarMargin_div_variance_le_next_ratio
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    (((mD beta hbeta.le) ^ 2 *
      Measure.real muD
        {U : CfgD | uD beta hbeta.le U < -(mD beta hbeta.le)})) / VD ≤
    (‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2) /
      (‖((SD beta hbeta.le) ^ n) fD‖ ^ 2) := by
  have hV : 0 < VD :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hN :=
    p4Q2PZ37AKD_originalAllPowers_energy_pos H beta hbeta n
  have hStep :=
    p4Q2PZ37AKD_originalAllPowers_HaarMargin_mul_energy_le_variance_next
      H beta hbeta n
  apply (div_le_div_iff₀ hV hN).2
  calc
    ((mD beta hbeta.le) ^ 2 *
      Measure.real muD
        {U : CfgD | uD beta hbeta.le U < -(mD beta hbeta.le)}) *
      ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 ≤
      VD * ‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2 := hStep
    _ = ‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2 * VD := by ring

/-- No claimed stepwise decay factor q below B/V can dominate the
genuine original Wilson source orbit at any integer power. Conditional
on qV<B; no H-uniform q or spectral gap is constructed. -/
theorem p4Q2PZ37AKD_originalAllPowers_no_subcritical_step_factor
    (beta : ℝ) (hbeta : 0 < beta) (q : ℝ)
    (hq :
      q * VD <
        (mD beta hbeta.le) ^ 2 *
          Measure.real muD
            {U : CfgD | uD beta hbeta.le U < -(mD beta hbeta.le)})
    (n : ℕ) :
    ¬ (‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2 ≤
      q * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2) := by
  let B : ℝ :=
    (mD beta hbeta.le) ^ 2 *
      Measure.real muD
        {U : CfgD | uD beta hbeta.le U < -(mD beta hbeta.le)}
  intro hUpper
  have hV : 0 < VD :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hN :
      0 < ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 :=
    p4Q2PZ37AKD_originalAllPowers_energy_pos H beta hbeta n
  have hStep :
      B * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 ≤
      VD * ‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2 :=
    p4Q2PZ37AKD_originalAllPowers_HaarMargin_mul_energy_le_variance_next
      H beta hbeta n
  have hUpperMul :
      VD * ‖((SD beta hbeta.le) ^ (n + 1)) fD‖ ^ 2 ≤
      VD * (q * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hUpper hV.le
  have hStrict :
      VD * (q * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2) <
      B * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 := by
    calc
      VD * (q * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2) =
          (q * VD) * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 := by ring
      _ < B * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2 :=
        mul_lt_mul_of_pos_right hq hN
  exact (lt_irrefl (B * ‖((SD beta hbeta.le) ^ n) fD‖ ^ 2))
    (lt_of_le_of_lt (hStep.trans hUpperMul) hStrict)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Seven genuine declarations, seven independent kernel axiom audits. -/
#print axioms MGAP4D.MathlibAnalytic.real_positive_logConvex_sequence_margin_step_akd
#print axioms MGAP4D.MathlibAnalytic.real_positive_logConvex_sequence_margin_ratio_akd
#print axioms MGAP4D.MathlibAnalytic.real_positive_logConvex_sequence_no_subcritical_step_akd
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_energy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_HaarMargin_mul_energy_le_variance_next
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_HaarMargin_div_variance_le_next_ratio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKD_originalAllPowers_no_subcritical_step_factor
