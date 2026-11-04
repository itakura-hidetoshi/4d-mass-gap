import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFiniteShellNetPackingV5_PZ37AFG
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFH — interval-certified original Wilson/Perron Haar shells

AFG gives a genuine finite-net filter of original SU(2) Wilson/Perron
threshold-shell centers, and an actual 2r-separated physical packing.
AFH introduces four rigorously bounded original finite-sample numbers
per center: lower/upper bounds on squared TRUE four-mode amplitude and
on the TRUE higher-character residual energy, with actual proof evidence.

For nonnegative lower threshold lo and lo <= hi, the two finite
interval checks

 etaLo < residualLower(a) - lo * amplitudeUpper(a)
 residualUpper(a) - hi * amplitudeLower(a) < -etaHi

guarantee the EXACT original robust signs at the same true boundary
configuration. This preserves the genuine joint Perron factor, transfer,
Gauss-law source, Haar law, FC envelope and full-link metric; it is not
an interval approximation substituted as the physical receiver.

The original AFG separated packing and AEA Haar ball floor then give
  |t| * kappa_H(r) <= nu_H(Bad_lo \ Bad_hi)
and an AFE/AFA upper-bound and GI/FC continuation. Strictly tightening
sound interval bounds cannot remove previously certified centers.
Conversely an explicit finite interval barrier can rule out such
CERTIFICATES without claiming absence of a true physical shell.

An exact-value interval embedding proves consistency and makes the
loss of completeness from coarse interval estimates explicit. No
actual numerical interval computation, unconditional strict sign
crossing, volume-uniform estimate, physical Hamiltonian gap, or
continuum 4D Yang--Mills mass gap is asserted. AEX no-go remains.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFH_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFH_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFH_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFH_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFH_probabilityG : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H
local notation "Bad" => p4Q2PZ37AFA_originalExceptionalBoundary H
local notation "Shell" => p4Q2PZ37AFF_originalExceptionalShell H
local notation "Robust" => p4Q2PZ37AFG_originalRobustShellCenters H
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AFH_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFH_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Four per-sample intervals bound the TRUE original squared amplitude
and TRUE original higher-character residual on the finite AFG net.
They are values together with actual physical proof evidence, not
unverified floating-point claims. -/
structure p4Q2PZ37AFH_originalIntervalEvidence
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  amplitudeLower :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  amplitudeUpper :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  residualLower :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  residualUpper :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hThetaLo : 0 ≤ lo
  hAmplitudeLower : ∀ a ∈ c.s,
    amplitudeLower a ≤
      (p4Q2PZ37ACM_originalCovarianceAmplitude H
        p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le e a)^2
  hAmplitudeUpper : ∀ a ∈ c.s,
    (p4Q2PZ37ACM_originalCovarianceAmplitude H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le e a)^2 ≤
        amplitudeUpper a
  hResidualLower : ∀ a ∈ c.s,
    residualLower a ≤
      p4Q2PZ37ACK_originalFourModeResidualEnergy H
        p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le e a
  hResidualUpper : ∀ a ∈ c.s,
    p4Q2PZ37ACK_originalFourModeResidualEnergy H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le e a ≤
        residualUpper a

/-- Finite interval check: both physical gap sign tests are obtained
by VERIFIED upper/lower arithmetic rather than evaluating an unproved
proxy transfer distribution. -/
def p4Q2PZ37AFH_originalIntervalRobustCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c) :
    Finset Pair :=
  c.s.filter (fun a =>
    c.etaLo < q.residualLower a - lo * q.amplitudeUpper a ∧
    q.residualUpper a - hi * q.amplitudeLower a < -c.etaHi)
local notation "Interval" => p4Q2PZ37AFH_originalIntervalRobustCenters H

/-- Interval lower residual minus upper amplitude bounds the TRUE
original Wilson/Perron residual gap from BELOW. -/
theorem p4Q2PZ37AFH_originalGap_lower_fromIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    q.residualLower a - lo * q.amplitudeUpper a ≤ Gap e lo a := by
  have hMul := mul_le_mul_of_nonneg_left
    (q.hAmplitudeUpper a ha) q.hThetaLo
  have hRes := q.hResidualLower a ha
  change q.residualLower a - lo * q.amplitudeUpper a ≤
    W b0 hb0 e a - lo * (A b0 hb0 e a)^2
  linarith only [hMul, hRes]

/-- Interval upper residual minus lower amplitude bounds the TRUE
original Wilson/Perron residual gap from ABOVE. -/
theorem p4Q2PZ37AFH_originalGap_upper_fromIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    Gap e hi a ≤ q.residualUpper a - hi * q.amplitudeLower a := by
  have hThetaHi : 0 ≤ hi := q.hThetaLo.trans c.hOrder
  have hMul := mul_le_mul_of_nonneg_left
    (q.hAmplitudeLower a ha) hThetaHi
  have hRes := q.hResidualUpper a ha
  change W b0 hb0 e a - hi * (A b0 hb0 e a)^2 ≤
    q.residualUpper a - hi * q.amplitudeLower a
  linarith only [hMul, hRes]

/-- Every finite interval candidate has BOTH strict authentic
physical signs, so the interval check has no false positives. -/
theorem p4Q2PZ37AFH_intervalCenter_trueSigns
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ Interval e c q) :
    c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi := by
  have haS := (Finset.mem_filter.mp ha).1
  have hn := (Finset.mem_filter.mp ha).2
  exact ⟨hn.1.trans_le
      (p4Q2PZ37AFH_originalGap_lower_fromIntervals H e c q a haS),
    (p4Q2PZ37AFH_originalGap_upper_fromIntervals H e c q a haS).trans_lt
      hn.2⟩

/-- The finite interval table is a verified SUBSET of AFG's exact
original robust shell center set, never a replacement for it. -/
theorem p4Q2PZ37AFH_intervalCenters_subset_originalRobust
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c) :
    Interval e c q ⊆ Robust e c := by
  intro a ha
  have hs := (Finset.mem_filter.mp ha).1
  exact Finset.mem_filter.mpr
    ⟨hs, p4Q2PZ37AFH_intervalCenter_trueSigns H e c q a ha⟩

/-- Any accepted finite interval center determines a genuine
original D_H ball that is contained in the TRUE shell. -/
theorem p4Q2PZ37AFH_intervalCenter_ball_subset_shell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ Interval e c q) :
    Ball a c.r ⊆ Shell e lo hi :=
  p4Q2PZ37AFG_robustCenter_ball_subset H e c a
    (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q ha)

/-- Interval-certified true shell balls carry the unchanged AEA
explicit positive H-dependent pair-Haar lower measure. -/
theorem p4Q2PZ37AFH_intervalCenter_floor_le_shellMass
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ Interval e c q) :
    p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
      Measure.real outer (Shell e lo hi) :=
  p4Q2PZ37AFG_robustCenter_floor_le_shell H e c a
    (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q ha)

/-- True original shell crossing at an accepted interval center
forces NONZERO genuine physical squared four-mode amplitude and a
STRICT separation of thresholds. A zero-amplitude point cannot cross. -/
theorem p4Q2PZ37AFH_intervalCenter_amplitude_pos_and_threshold_strict
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ Interval e c q) :
    0 < (A b0 hb0 e a)^2 ∧ lo < hi := by
  obtain ⟨hLow, hHigh⟩ :=
    p4Q2PZ37AFH_intervalCenter_trueSigns H e c q a ha
  have hLowPos : 0 < Gap e lo a := c.hEtaLo.trans hLow
  have hHighNeg : Gap e hi a < 0 := by linarith only [hHigh, c.hEtaHi]
  change 0 < W b0 hb0 e a - lo * (A b0 hb0 e a)^2 at hLowPos
  change W b0 hb0 e a - hi * (A b0 hb0 e a)^2 < 0 at hHighNeg
  have hAmpPos : 0 < (A b0 hb0 e a)^2 := by
    by_contra h
    have hZero : (A b0 hb0 e a)^2 = 0 :=
      le_antisymm (le_of_not_gt h) (sq_nonneg _)
    rw [hZero] at hLowPos hHighNeg
    nlinarith only [hLowPos, hHighNeg]
  have hThetaStrict : lo < hi := by
    by_contra h
    have hEq : lo = hi :=
      le_antisymm c.hOrder (le_of_not_gt h)
    rw [hEq] at hLowPos
    linarith only [hLowPos, hHighNeg]
  exact ⟨hAmpPos, hThetaStrict⟩

/-- The true Wilson/Perron receiver residual-to-amplitude-squared
ratio is strictly INSIDE the certified threshold shell. This is
only stated where the original amplitude square is positive. -/
theorem p4Q2PZ37AFH_intervalCenter_trueRatio_bracket
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (a : Pair) (ha : a ∈ Interval e c q) :
    lo < W b0 hb0 e a / (A b0 hb0 e a)^2 ∧
      W b0 hb0 e a / (A b0 hb0 e a)^2 < hi := by
  obtain ⟨hLow, hHigh⟩ :=
    p4Q2PZ37AFH_intervalCenter_trueSigns H e c q a ha
  have hAmp := (p4Q2PZ37AFH_intervalCenter_amplitude_pos_and_threshold_strict
    H e c q a ha).1
  have hLo : lo * (A b0 hb0 e a)^2 < W b0 hb0 e a := by
    change c.etaLo <
      W b0 hb0 e a - lo * (A b0 hb0 e a)^2 at hLow
    linarith only [hLow, c.hEtaLo]
  have hHi : W b0 hb0 e a < hi * (A b0 hb0 e a)^2 := by
    change W b0 hb0 e a -
      hi * (A b0 hb0 e a)^2 < -c.etaHi at hHigh
    linarith only [hHigh, c.hEtaHi]
  exact ⟨(lt_div_iff₀ hAmp).mpr hLo,
    (div_lt_iff₀ hAmp).mpr hHi⟩

/-- Strict tightening (no weakening) of the four certified physical
interval bounds cannot make an already certified shell center fail.
The same actual original finite net and physical receiver are used. -/
theorem p4Q2PZ37AFH_intervalCenters_mono_of_tightening
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q₁ q₂ : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (hAmpLo : ∀ a ∈ c.s, q₁.amplitudeLower a ≤ q₂.amplitudeLower a)
    (hAmpHi : ∀ a ∈ c.s, q₂.amplitudeUpper a ≤ q₁.amplitudeUpper a)
    (hResLo : ∀ a ∈ c.s, q₁.residualLower a ≤ q₂.residualLower a)
    (hResHi : ∀ a ∈ c.s, q₂.residualUpper a ≤ q₁.residualUpper a) :
    Interval e c q₁ ⊆ Interval e c q₂ := by
  intro a ha
  have haS := (Finset.mem_filter.mp ha).1
  obtain ⟨hOldLo, hOldHi⟩ := (Finset.mem_filter.mp ha).2
  have hThetaHi : 0 ≤ hi := q₁.hThetaLo.trans c.hOrder
  have hMulLo :=
    mul_le_mul_of_nonneg_left (hAmpHi a haS) q₁.hThetaLo
  have hMulHi :=
    mul_le_mul_of_nonneg_left (hAmpLo a haS) hThetaHi
  refine Finset.mem_filter.mpr ⟨haS, ?_⟩
  constructor
  · linarith only [hOldLo, hResLo a haS, hMulLo]
  · linarith only [hOldHi, hResHi a haS, hMulHi]

/-- Explicit finite obstruction: if EACH original sample fails at
least one sound strict interval margin, this particular numeric
certificate has no accepted centers. It does NOT prove true-shell
emptiness or absence of more precise interval certificates. -/
theorem p4Q2PZ37AFH_intervalCenters_empty_of_barrier
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (hBarrier : ∀ a ∈ c.s,
      q.residualLower a - lo * q.amplitudeUpper a ≤ c.etaLo ∨
      -c.etaHi ≤ q.residualUpper a - hi * q.amplitudeLower a) :
    Interval e c q = ∅ := by
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have haS := (Finset.mem_filter.mp ha).1
    obtain ⟨hLo, hHi⟩ := (Finset.mem_filter.mp ha).2
    rcases hBarrier a haS with h | h
    · exact False.elim ((not_lt_of_ge h) hLo)
    · exact False.elim ((not_lt_of_ge h) hHi)
  · intro ha
    simp at ha

/-- The genuine finite greedy algorithm extracts a disjoint packing
from INTERVAL-certified centers, not from uncertified gap estimates. -/
theorem p4Q2PZ37AFH_intervalPacking_exists
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c) :
    ∃ t : Finset Pair, t ⊆ Interval e c q ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b) ∧
      (∀ a ∈ Interval e c q, ∃ b ∈ t, D a b < 2 * c.r) ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) := by
  obtain ⟨t, ht, hSep, hCover⟩ :=
    p4Q2PZ37AFD_finiteGreedySeparatedSubcover
      (Interval e c q) D c.r c.hR
      (p4Q2PZ37ADL_originalFullDistance_self H)
      (p4Q2PZ37ADL_originalFullDistance_symm H)
  have hPhysical : t ⊆ Robust e c :=
    ht.trans (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q)
  exact ⟨t, ht, hSep, hCover,
    p4Q2PZ37AFG_robustPacking_mass_lower H e c t hPhysical hSep⟩

/-- A nonempty interval-certified finite set gives positive,
explicit and GENUINE original Haar shell mass through separated
packing, without asserting any numerical cardinality beforehand. -/
theorem p4Q2PZ37AFH_intervalNonempty_positivePackedShell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (hNonempty : (Interval e c q).Nonempty) :
    ∃ t : Finset Pair,
      t ⊆ Interval e c q ∧
      0 < (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) := by
  obtain ⟨t, ht, _hSep, hCover, hFloor⟩ :=
    p4Q2PZ37AFH_intervalPacking_exists H e c q
  obtain ⟨a, ha⟩ := hNonempty
  obtain ⟨b, hb, _hNear⟩ := hCover a ha
  have hCardNat : 0 < t.card := Finset.card_pos.mpr ⟨b, hb⟩
  have hCard : (0 : ℝ) < (t.card : ℝ) := by exact_mod_cast hCardNat
  have hRad : 0 < p4Q2PZ37AFD_originalHaarBallFloor H c.r :=
    p4Q2PZ37AEA_explicitFloor_pos H c.r c.hR
  exact ⟨t, ht, mul_pos hCard hRad, hFloor⟩

/-- Canonical EXACT-VALUE special case of interval evidence. Its
existence is mathematical, NOT a numerical computation or interval
arithmetic certification of the original finite net. -/
def p4Q2PZ37AFH_originalExactIntervalEvidence
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hTheta : 0 ≤ lo) :
    p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c where
  amplitudeLower := fun a => (A b0 hb0 e a)^2
  amplitudeUpper := fun a => (A b0 hb0 e a)^2
  residualLower := fun a => W b0 hb0 e a
  residualUpper := fun a => W b0 hb0 e a
  hThetaLo := hTheta
  hAmplitudeLower := by intro a _ha; exact le_refl _
  hAmplitudeUpper := by intro a _ha; exact le_refl _
  hResidualLower := by intro a _ha; exact le_refl _
  hResidualUpper := by intro a _ha; exact le_refl _

/-- With *exact* original physical values the interval filter agrees
with AFG's original true-gap filter. Coarse intervals only reduce it,
as certified above; this records the precise conditional completeness
boundary. -/
theorem p4Q2PZ37AFH_exactIntervals_eq_originalRobust
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hTheta : 0 ≤ lo) :
    Interval e c (p4Q2PZ37AFH_originalExactIntervalEvidence H e c hTheta) =
      Robust e c := by
  rfl

/-- Original true-gap strict crossing plus a sufficiently fine net
is visible in the exact-value interval certificate. This does not
claim availability of actual finite error-controlled numeric values. -/
theorem p4Q2PZ37AFH_exactIntervals_detect_strongOriginalPoint
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hTheta : 0 ≤ lo) (z : Pair)
    (hLow : 2 * c.etaLo < Gap e lo z)
    (hHigh : Gap e hi z < -(2 * c.etaHi)) :
    (Interval e c
      (p4Q2PZ37AFH_originalExactIntervalEvidence H e c hTheta)).Nonempty := by
  rw [p4Q2PZ37AFH_exactIntervals_eq_originalRobust H e c hTheta]
  exact p4Q2PZ37AFG_originalStrongShellPoint_detected H e c z hLow hHigh

/-- A verified interval-selected separated packing controls the
exact original bad boundary at the target threshold using ONLY the
old authentic AFG+AFE certificate function. -/
theorem p4Q2PZ37AFH_intervalPacking_originalBadMass_upper
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (t : Finset Pair)
    (baseScales topScales : List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Interval e c q)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi) :
    Measure.real outer (Bad e hi) ≤
      p4Q2PZ37AFG_originalPackedShellBudget H e c t baseScales topScales := by
  exact p4Q2PZ37AFG_originalPackedShellHaarMass_upper
    H e c t baseScales topScales
    (hSelected.trans
      (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q))
    hSep hBase hTop

/-- The exact original AFA GI mean budget becomes positive only if
the independently verified interval-sourced Haar upper certificate
also passes the original numerical 64 four-moment condition. -/
theorem p4Q2PZ37AFH_intervalPacking_gives_positiveBudget
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (t : Finset Pair)
    (baseScales topScales : List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Interval e c q)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hNumeric : hi * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFG_originalPackedShellBudget H e c t baseScales topScales <
          64 * A4 e) :
    0 < Budget b0 hb0 e := by
  exact p4Q2PZ37AFG_originalPackedShell_gives_positiveBudget
    H e c t baseScales topScales (q.hThetaLo.trans c.hOrder)
    (hSelected.trans
      (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q))
    hSep hBase hTop hNumeric

/-- Signed two-posterior ORIGINAL Wilson source GI is nonzero on a
positive real pair-Haar open region when the same independent
numerical mean test succeeds. -/
theorem p4Q2PZ37AFH_intervalPacking_gives_openGI
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (t : Finset Pair)
    (baseScales topScales : List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Interval e c q)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hNumeric : hi * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFG_originalPackedShellBudget H e c t baseScales topScales <
          64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37AFG_originalPackedShell_gives_openGI
    H e c t baseScales topScales (q.hThetaLo.trans c.hOrder)
    (hSelected.trans
      (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q))
    hSep hBase hTop hNumeric

/-- The strictly stronger original FC certificate additionally needs
INDEPENDENT true physical unused variance slack, not only interval
control of the exceptional residual shell. -/
theorem p4Q2PZ37AFH_intervalPackingFC_gives_trueFC
    (e : Link) {lo hi : ℝ} (sigma : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (t : Finset Pair)
    (baseScales topScales : List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Interval e c q)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumeric : (hi + sigma) * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFG_originalPackedShellBudget H e c t baseScales topScales <
          64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  exact p4Q2PZ37AFG_originalPackedShellFC_gives_trueFC
    H e sigma c t baseScales topScales (q.hThetaLo.trans c.hOrder)
    (hSelected.trans
      (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q))
    hSep hBase hTop hSlack hNumeric

/-- A failed genuine mean GI certificate transfers AFA's exact
necessary exceptional Haar mass floor to every sound numeric interval
packing. This is NOT a physical Yang--Mills no-go. -/
theorem p4Q2PZ37AFH_nonpositiveBudget_intervalPacking_floor
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (q : p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c)
    (t : Finset Pair)
    (baseScales topScales : List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Interval e c q)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - hi) * A4 e) / (B b0 hb0)^2 ≤
      p4Q2PZ37AFG_originalPackedShellBudget H e c t baseScales topScales := by
  exact p4Q2PZ37AFG_nonpositiveBudget_packedShell_floor
    H e c t baseScales topScales (q.hThetaLo.trans c.hOrder)
    (hSelected.trans
      (p4Q2PZ37AFH_intervalCenters_subset_originalRobust H e c q))
    hSep hBase hTop hNonpos

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_originalGap_lower_fromIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_originalGap_upper_fromIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenter_trueSigns
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenters_subset_originalRobust
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenter_ball_subset_shell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenter_floor_le_shellMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenter_amplitude_pos_and_threshold_strict
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenter_trueRatio_bracket
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenters_mono_of_tightening
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalCenters_empty_of_barrier
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalPacking_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalNonempty_positivePackedShell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_exactIntervals_eq_originalRobust
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_exactIntervals_detect_strongOriginalPoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalPacking_originalBadMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalPacking_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalPacking_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_intervalPackingFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFH_nonpositiveBudget_intervalPacking_floor
