import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalClosedThresholdPeakV5_PZ37ADA

/-!
# P4-Q2-PZ37ADB — genuinely dimensionless Wilson signal/residual budget

Append-only, on the SAME interacting finite-volume Wilson SU(2) receiver.
Preserve the centered Gauss-law physical source, original FF link receiver,
true Perron ground representative, updated transfer, actual two posteriors,
original physical link e and original boundary pair-Haar measure.

Write X=B²>0 for the original FC receiver variance cap and define
 u=16*S/X (genuine original four-coefficient covariance energy share),
 v=Wbar/X (genuine original higher-SU(2)-Haar residual share),
 tau=(exp(64*b)-1)²>0.
The original ACK variance identity and FC cap imply, with NO new
physical hypotheses, 0<u<=1, 0<=v and u+v<=1.
The original ACN Haar-mass floor becomes F=u/(2-u), and ADA's interior
optimizer feasibility condition becomes exactly
    F > C/(C+32*S)  iff  u² > tau*(1-u).
Independently, ACP's exact ORIGINAL mean GI SQUARED certificate test is
    Budget>0  iff  tau*v < 4*u.
Since v<=1-u, a purely dimensionless SUFFICIENT physical test is
    tau*(1-u)<4*u, equivalently u>tau/(tau+4).
The stronger ADA interior feasibility condition u²>tau*(1-u)
already implies the positive ORIGINAL mean certificate using the true
physical residual-share budget, even when ADA's particular ACZ
moment-overlap peak remains nonpositive.
This is NOT a proof that the actual Wilson model satisfies either
condition; nor is the squared certificate identified with signed GI.

We retain physical finite-H dependence and prove the reverse numerical
obstruction when the original mean certificate is nonpositive. No
volume-uniform coercivity or 4D continuum Yang–Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "μ" => normalizedCompactHaar G
local notation "Var" => CompactEnergyMismatchMoment.variance μ
local instance p4Q2PZ37ADB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADB_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADB_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADB_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADB_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADB_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "Rec" => p4Q2PZ37ABZ_originalReceiverSection H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Vbar" => p4Q2PZ37ACK_originalReceiverVarianceMoment H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "C" => p4Q2PZ37ACW_originalNegativeFCBudget H
local notation "F" => p4Q2PZ37ACY_originalFourModeMassFloor H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local instance p4Q2PZ37ADB_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADB_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Actual first-four signal energy as a fraction of the original FC
variance envelope, NOT a new Haar receiver or assumed distribution. -/
def p4Q2PZ37ADB_originalSignalFCFraction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (16 * S b hb e) / (B b hb) ^ 2
local notation "u" => p4Q2PZ37ADB_originalSignalFCFraction H

/-- Actual orthogonal higher-Haar remainder mean divided by the very
same original receiver FC squared cap. -/
def p4Q2PZ37ADB_originalResidualFCFraction
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  Wbar b hb e / (B b hb) ^ 2
local notation "v" => p4Q2PZ37ADB_originalResidualFCFraction H

/-- Dimensionless physical quadratic feasibility margin for ADA's
closed-form optimal positive discriminant threshold. -/
def p4Q2PZ37ADB_originalQuadraticFeasibilityMargin
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (u b hb e) ^ 2 - tau b * (1 - u b hb e)

/-- Elementary *exact* first-four Haar mass-floor normalization. -/
theorem p4Q2PZ37ADB_realHaarFloor_normalize
    (x s : ℝ) (hx : 0 < x) (hs : 0 < s) (hcap : 16 * s ≤ x) :
    4 * s / (x / 2 - 4 * s) =
      (16 * s / x) / (2 - 16 * s / x) := by
  have hden : 0 < x / 2 - 4 * s := by linarith only [hcap, hs]
  have hfrac : 16 * s / x ≤ 1 :=
    (div_le_iff₀ hx).mpr (by simpa using hcap)
  have htwo : 0 < 2 - 16 * s / x := by linarith only [hfrac]
  have hne1 : x - s * 8 ≠ 0 := by
    have hpos : 0 < x - s * 8 := by linarith only [hden]
    exact ne_of_gt hpos
  have hne2 : x * 2 - s * 16 ≠ 0 := by
    have hpos : 0 < x * 2 - s * 16 := by linarith only [hden]
    exact ne_of_gt hpos
  field_simp [ne_of_gt hx, ne_of_gt hden, ne_of_gt htwo, hne1, hne2]
  have hcancel : (x - s * 8) * (x - s * 8)⁻¹ = 1 := by
    simpa only [div_eq_mul_inv] using (div_self hne1)
  calc
    x * (x - s * 8)⁻¹ * 16 - s * (x - s * 8)⁻¹ * 128 =
        16 * ((x - s * 8) * (x - s * 8)⁻¹) := by ring
    _ = 16 := by simp only [hcancel, mul_one]

/-- Scaling by the SAME original positive FC cap cancels precisely
from the Perron negative-region threshold ratio. -/
theorem p4Q2PZ37ADB_realNegativeRatio_normalize
    (x s t : ℝ) (hx : 0 < x) (hs : 0 < s) (ht : 0 < t) :
    (t * x) / (t * x + 32 * s) =
      t / (t + 2 * (16 * s / x)) := by
  have hden : 0 < t * x + 32 * s := by positivity
  have htwo : 0 < t + 2 * (16 * s / x) := by positivity
  field_simp [ne_of_gt hx, ne_of_gt hden, ne_of_gt htwo]; ring

/-- No square roots: the exact ADA interior optimum criterion is just
a quadratic signal versus posterior-gap inequality on u in (0,1]. -/
theorem p4Q2PZ37ADB_realRatio_iff_quadratic
    (u₀ t : ℝ) (hu : 0 < u₀) (huOne : u₀ ≤ 1) (ht : 0 < t) :
    t / (t + 2 * u₀) < u₀ / (2 - u₀) ↔
      t * (1 - u₀) < u₀ ^ 2 := by
  have hd1 : 0 < t + 2 * u₀ := by linarith only [ht, hu]
  have hd2 : 0 < 2 - u₀ := by linarith only [huOne]
  constructor
  · intro h
    have hcross := (div_lt_div_iff₀ hd1 hd2).mp h
    nlinarith only [hcross]
  · intro h
    apply (div_lt_div_iff₀ hd1 hd2).mpr
    nlinarith only [h]

/-- Exact scalar equivalence for ACP's mean-certificate comparison. -/
theorem p4Q2PZ37ADB_realResidualRatio_iff
    (x s w t : ℝ) (hx : 0 < x) :
    t * (w / x) < 4 * (16 * s / x) ↔
      t * w < 64 * s := by
  have ha : t * (w / x) = (t * w) / x := by ring
  have hb : 4 * (16 * s / x) = (64 * s) / x := by ring
  rw [ha, hb, div_lt_div_iff₀ hx hx]
  constructor
  · intro hh
    by_contra hn
    have hrev : 64 * s ≤ t * w := le_of_not_gt hn
    have hscaled := mul_le_mul_of_nonneg_right hrev hx.le
    exact (not_le_of_gt hh) hscaled
  · intro hh
    exact mul_lt_mul_of_pos_right hh hx

/-- An even simpler single-number threshold for the original Wilson
mean certificate, not a claim about actual data at arbitrary b,H. -/
theorem p4Q2PZ37ADB_realLinearThreshold_iff
    (u₀ t : ℝ) (ht : 0 < t) :
    t / (t + 4) < u₀ ↔ t * (1 - u₀) < 4 * u₀ := by
  have hden : 0 < t + 4 := by linarith only [ht]
  constructor
  · intro h
    have hc := (div_lt_iff₀ hden).mp h
    nlinarith only [hc]
  · intro h
    apply (div_lt_iff₀ hden).mpr
    nlinarith only [h]

/-- The same ORIGINAL physical FC receiver envelope has positive
square, since ACK's strictly positive covariance S cannot exceed it. -/
theorem p4Q2PZ37ADB_originalFCsq_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < (B b hb.le) ^ 2 := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b hb e
  have hcap := p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
    H b hb.le e
  nlinarith only [hs, hcap]

/-- Genuine four-mode FC fraction lies in (0,1] at every positive
coupling and finite-volume physical link. -/
theorem p4Q2PZ37ADB_originalSignalFraction_pos_le_one
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < u b hb.le e ∧ u b hb.le e ≤ 1 := by
  have hx := p4Q2PZ37ADB_originalFCsq_pos H b hb e
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b hb e
  have hcap := p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
    H b hb.le e
  change 0 < 16 * S b hb.le e / (B b hb.le) ^ 2 ∧
    16 * S b hb.le e / (B b hb.le) ^ 2 ≤ 1
  constructor
  · exact div_pos (mul_pos (by norm_num) hs) hx
  · apply (div_le_iff₀ hx).mpr
    nlinarith only [hcap]

/-- Genuine higher-SU(2)-Haar remainder share is nonnegative. -/
theorem p4Q2PZ37ADB_originalResidualFraction_nonneg
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 ≤ v b hb.le e := by
  exact div_nonneg
    (p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e)
    (p4Q2PZ37ADB_originalFCsq_pos H b hb e).le

/-- The ORIGINAL boundary pair-Haar mean of receiver variance is
bounded by the SAME unchanged original FF receiver FC envelope. -/
theorem p4Q2PZ37ADB_originalVarianceMoment_le_FC
    (b : ℝ) (hb : 0 ≤ b) (e : Link) :
    Vbar b hb e ≤ (B b hb) ^ 2 := by
  change (∫ z : Pair, Var (Rec b hb f₀ e z) ∂outer) ≤ (B b hb) ^ 2
  have hi : Integrable (fun z : Pair => Var (Rec b hb f₀ e z)) outer :=
    (p4Q2PZ37ACD_originalReceiver_variance_continuous
      H b hb f₀ e).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    (∫ z : Pair, Var (Rec b hb f₀ e z) ∂outer) ≤
        ∫ _z : Pair, (B b hb) ^ 2 ∂outer := by
      apply integral_mono hi (integrable_const _)
      intro z
      exact p4Q2PZ37ACA_originalReceiver_variance_le_FC H b hb f₀ e z
    _ = (B b hb) ^ 2 := by simp

/-- No independent randomness: the TWO genuine original Haar energy
shares consume at most the SAME single-link FC squared variance budget. -/
theorem p4Q2PZ37ADB_originalSignalResidualShares_le_one
    (b : ℝ) (hb : 0 < b) (e : Link) :
    u b hb.le e + v b hb.le e ≤ 1 := by
  have hx := p4Q2PZ37ADB_originalFCsq_pos H b hb e
  have hV := p4Q2PZ37ADB_originalVarianceMoment_le_FC H b hb.le e
  have hDecomp := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e
  have hSum : 16 * S b hb.le e + Wbar b hb.le e ≤ (B b hb.le) ^ 2 := by
    linarith only [hV, hDecomp]
  change 16 * S b hb.le e / (B b hb.le) ^ 2 +
    Wbar b hb.le e / (B b hb.le) ^ 2 ≤ 1
  rw [← add_div]
  exact (div_le_iff₀ hx).mpr (by simpa only [one_mul] using hSum)

/-- Sharper original residual moment FC bound with the *four-mode*
budget explicitly deducted; this is stronger than Wbar<=B². -/
theorem p4Q2PZ37ADB_originalResidualMoment_le_FC_minus_four
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Wbar b hb.le e ≤ (B b hb.le) ^ 2 - 16 * S b hb.le e := by
  have hV := p4Q2PZ37ADB_originalVarianceMoment_le_FC H b hb.le e
  have hEq := p4Q2PZ37ACK_originalVarianceMoment_eq H b hb.le e
  linarith only [hV, hEq]

/-- The same normalized residual share is bounded by the unused
original positive FC four-mode fraction, NOT by a new physical bound. -/
theorem p4Q2PZ37ADB_originalResidualShare_le_unusedSignal
    (b : ℝ) (hb : 0 < b) (e : Link) :
    v b hb.le e ≤ 1 - u b hb.le e := by
  have h := p4Q2PZ37ADB_originalSignalResidualShares_le_one H b hb e
  linarith only [h]

/-- ACN's sharp original four-mode HIGH-SIGNAL pair-Haar mass floor
depends on original FC data only through the dimensionless u. -/
theorem p4Q2PZ37ADB_originalHaarFloor_eq_signalFraction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    F b hb.le e = u b hb.le e / (2 - u b hb.le e) := by
  have hx := p4Q2PZ37ADB_originalFCsq_pos H b hb e
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have hcap := p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
    H b hb.le e
  have h := p4Q2PZ37ADB_realHaarFloor_normalize
    ((B b hb.le) ^ 2) (S b hb.le e) hx hs (by nlinarith only [hcap])
  simpa only [p4Q2PZ37ACY_originalFourModeMassFloor,
    p4Q2PZ37ADB_originalSignalFCFraction] using h

/-- ADA's original negative FC ratio has exactly the normalized
t/(t+2u) form, keeping the same physical Perron gap t=tau(b). -/
theorem p4Q2PZ37ADB_originalNegativeThresholdRatio_eq
    (b : ℝ) (hb : 0 < b) (e : Link) :
    C b hb.le / (C b hb.le + 32 * S b hb.le e) =
      tau b / (tau b + 2 * u b hb.le e) := by
  have hx := p4Q2PZ37ADB_originalFCsq_pos H b hb e
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos H b hb e
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have h := p4Q2PZ37ADB_realNegativeRatio_normalize
    ((B b hb.le) ^ 2) (S b hb.le e) (tau b) hx hs ht
  simpa only [p4Q2PZ37ACW_originalNegativeFCBudget,
    p4Q2PZ37ADB_originalSignalFCFraction] using h

/-- Exact physical criterion for ADA's INTERIOR sqrt optimizer is an
elementary QUADRATIC comparison in the actual dimensionless energy u. -/
theorem p4Q2PZ37ADB_originalADARatio_iff_quadratic
    (b : ℝ) (hb : 0 < b) (e : Link) :
    (C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e) ↔
      0 < p4Q2PZ37ADB_originalQuadraticFeasibilityMargin H b hb.le e := by
  have hu := p4Q2PZ37ADB_originalSignalFraction_pos_le_one H b hb e
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  rw [p4Q2PZ37ADB_originalNegativeThresholdRatio_eq H b hb e,
    p4Q2PZ37ADB_originalHaarFloor_eq_signalFraction H b hb e]
  change (tau b / (tau b + 2 * u b hb.le e) <
    u b hb.le e / (2 - u b hb.le e)) ↔
    0 < (u b hb.le e) ^ 2 - tau b * (1 - u b hb.le e)
  simpa only [sub_pos] using
    p4Q2PZ37ADB_realRatio_iff_quadratic
      (u b hb.le e) (tau b) hu.1 hu.2 ht

/-- The exact ACP mean GI squared-certificate test is simply the
dimensionless higher Haar residual fraction versus the four-signal share. -/
theorem p4Q2PZ37ADB_originalGIMeanBudget_pos_iff_dimensionless
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < Budget b hb.le e ↔
      tau b * v b hb.le e < 4 * u b hb.le e := by
  have hx := p4Q2PZ37ADB_originalFCsq_pos H b hb e
  calc
    0 < Budget b hb.le e ↔
        tau b * Wbar b hb.le e < 64 * S b hb.le e :=
      p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual H b hb e
    _ ↔ tau b * v b hb.le e < 4 * u b hb.le e := by
      simpa only [p4Q2PZ37ADB_originalSignalFCFraction,
        p4Q2PZ37ADB_originalResidualFCFraction] using
        (p4Q2PZ37ADB_realResidualRatio_iff
          ((B b hb.le) ^ 2) (S b hb.le e) (Wbar b hb.le e) (tau b) hx).symm

/-- Failure of the original mean GI squared certificate is exactly a
dimensionless residual-share obstruction, NOT actual signed GI vanishing. -/
theorem p4Q2PZ37ADB_originalGIMeanBudget_nonpos_iff_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Budget b hb.le e ≤ 0 ↔
      4 * u b hb.le e ≤ tau b * v b hb.le e := by
  have hIff := p4Q2PZ37ADB_originalGIMeanBudget_pos_iff_dimensionless
    H b hb e
  constructor
  · intro hn
    by_contra h
    have hsmall : tau b * v b hb.le e < 4 * u b hb.le e :=
      lt_of_not_ge h
    exact (not_lt_of_ge hn) (hIff.mpr hsmall)
  · intro hn
    by_contra h
    have hpos : 0 < Budget b hb.le e := lt_of_not_ge h
    exact (not_lt_of_ge hn) (hIff.mp hpos)

/-- Exact dimensionless physical signal threshold for a certificate
from the FC *worst-case residual*. No Haar independence assumption. -/
theorem p4Q2PZ37ADB_originalLinearSignalThreshold_iff
    (b : ℝ) (hb : 0 < b) (e : Link) :
    tau b / (tau b + 4) < u b hb.le e ↔
      tau b * (1 - u b hb.le e) < 4 * u b hb.le e := by
  exact p4Q2PZ37ADB_realLinearThreshold_iff
    (u b hb.le e) (tau b)
    (p4Q2PZ37ACZ_originalPosteriorGap_pos b hb)

/-- With the actual physical residual variance bound, a single
direct inequality in u and tau SUFFICES for positive ACO GI budget. -/
theorem p4Q2PZ37ADB_originalLinearSignalThreshold_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hSignal : tau b * (1 - u b hb.le e) < 4 * u b hb.le e) :
    0 < Budget b hb.le e := by
  have hv := p4Q2PZ37ADB_originalResidualShare_le_unusedSignal H b hb e
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have hMul := mul_le_mul_of_nonneg_left hv ht.le
  apply (p4Q2PZ37ADB_originalGIMeanBudget_pos_iff_dimensionless
    H b hb e).mpr
  linarith only [hSignal, hMul]

/-- The same physical single-number condition gives a true OPEN,
positive pair-Haar-mass nonzero SIGNED two-posterior GI response region. -/
theorem p4Q2PZ37ADB_originalLinearSignalThreshold_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hSignal : tau b * (1 - u b hb.le e) < 4 * u b hb.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ADB_originalLinearSignalThreshold_gives_positiveBudget
      H b hb e hSignal)

/-- Strong ADA optimizer FEASIBILITY u²>tau*(1-u) alone implies
positive original mean GI squared certificate by the true ACK remainder
budget v<=1-u, whether or not ADA's ACZ overlap peak is positive. -/
theorem p4Q2PZ37ADB_originalQuadraticFeasibility_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hQuad : tau b * (1 - u b hb.le e) < (u b hb.le e) ^ 2) :
    0 < Budget b hb.le e := by
  have hu := p4Q2PZ37ADB_originalSignalFraction_pos_le_one H b hb e
  have hProduct : 0 ≤ u b hb.le e * (1 - u b hb.le e) :=
    mul_nonneg hu.1.le (sub_nonneg.mpr hu.2)
  have hSq : (u b hb.le e) ^ 2 ≤ u b hb.le e := by
    nlinarith only [hProduct]
  have hFour : u b hb.le e ≤ 4 * u b hb.le e := by
    linarith only [hu.1]
  have hSignal : tau b * (1 - u b hb.le e) < 4 * u b hb.le e :=
    lt_of_lt_of_le hQuad (hSq.trans hFour)
  exact p4Q2PZ37ADB_originalLinearSignalThreshold_gives_positiveBudget
    H b hb e hSignal

/-- The ADA *INTERIOR* optimizer criterion, even without its peak
surplus assumption, implies positivity of the ORIGINAL squared GI mean.
This shortcut uses the genuine Wilson variance decomposition. -/
theorem p4Q2PZ37ADB_originalADAFeasibility_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFeasible : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e) :
    0 < Budget b hb.le e := by
  have hQuad :=
    (p4Q2PZ37ADB_originalADARatio_iff_quadratic H b hb e).mp hFeasible
  unfold p4Q2PZ37ADB_originalQuadraticFeasibilityMargin at hQuad
  exact p4Q2PZ37ADB_originalQuadraticFeasibility_gives_positiveBudget
    H b hb e (sub_pos.mp hQuad)

/-- An OPEN positive original pair-Haar set of genuine nonzero signed
GI response follows conditionally from ADA optimizer feasibility alone. -/
theorem p4Q2PZ37ADB_originalADAFeasibility_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFeasible : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ADB_originalADAFeasibility_gives_positiveBudget
      H b hb e hFeasible)

/-- A genuinely NONPOSITIVE original GI mean certificate necessarily
satisfies the complement-bound obstruction involving NO Wbar variable:
4u<=tau*(1-u), and so u<=tau/(tau+4). -/
theorem p4Q2PZ37ADB_nonpositiveBudget_forces_linearSignalObstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    4 * u b hb.le e ≤ tau b * (1 - u b hb.le e) := by
  have hOb := (p4Q2PZ37ADB_originalGIMeanBudget_nonpos_iff_obstruction
    H b hb e).mp hNonpos
  have hv := p4Q2PZ37ADB_originalResidualShare_le_unusedSignal H b hb e
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have hm := mul_le_mul_of_nonneg_left hv ht.le
  exact hOb.trans hm

/-- Exact stronger quadratic obstruction of ADA method when the
physical GI squared mean certificate itself is nonpositive. -/
theorem p4Q2PZ37ADB_nonpositiveBudget_forces_quadraticObstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0) :
    (u b hb.le e) ^ 2 ≤ tau b * (1 - u b hb.le e) := by
  have hu := p4Q2PZ37ADB_originalSignalFraction_pos_le_one H b hb e
  have hprod : 0 ≤ u b hb.le e * (1 - u b hb.le e) :=
    mul_nonneg hu.1.le (sub_nonneg.mpr hu.2)
  have hs : (u b hb.le e) ^ 2 ≤ u b hb.le e := by
    nlinarith only [hprod]
  have hm := p4Q2PZ37ADB_nonpositiveBudget_forces_linearSignalObstruction
    H b hb e hNonpos
  have hfour : u b hb.le e ≤ 4 * u b hb.le e := by
    linarith only [hu.1]
  exact (hs.trans hfour).trans hm

/-- The original FC boundary saturation u=1 would force the actual
higher-Haar remainder mean to vanish, not just become small. -/
theorem p4Q2PZ37ADB_fullSignalShare_forces_zeroResidual
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFull : u b hb.le e = 1) :
    v b hb.le e = 0 := by
  have hn := p4Q2PZ37ADB_originalResidualFraction_nonneg H b hb e
  have hbgt := p4Q2PZ37ADB_originalSignalResidualShares_le_one H b hb e
  linarith only [hFull, hn, hbgt]

/-- Full utilization of the original receiver FC covariance budget
would also force a strict GI squared mean certificate, conditionally. -/
theorem p4Q2PZ37ADB_fullSignalShare_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hFull : u b hb.le e = 1) :
    0 < Budget b hb.le e := by
  have hv := p4Q2PZ37ADB_fullSignalShare_forces_zeroResidual
    H b hb e hFull
  apply (p4Q2PZ37ADB_originalGIMeanBudget_pos_iff_dimensionless
    H b hb e).mpr
  rw [hFull, hv]
  norm_num

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_realHaarFloor_normalize
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_realNegativeRatio_normalize
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_realRatio_iff_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_realResidualRatio_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_realLinearThreshold_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalFCsq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalSignalFraction_pos_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalResidualFraction_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalVarianceMoment_le_FC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalSignalResidualShares_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalResidualMoment_le_FC_minus_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalResidualShare_le_unusedSignal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalHaarFloor_eq_signalFraction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalNegativeThresholdRatio_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalADARatio_iff_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalGIMeanBudget_pos_iff_dimensionless
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalGIMeanBudget_nonpos_iff_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalLinearSignalThreshold_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalLinearSignalThreshold_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalLinearSignalThreshold_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalQuadraticFeasibility_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalADAFeasibility_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_originalADAFeasibility_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_nonpositiveBudget_forces_linearSignalObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_nonpositiveBudget_forces_quadraticObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_fullSignalShare_forces_zeroResidual
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADB_fullSignalShare_gives_positiveBudget
