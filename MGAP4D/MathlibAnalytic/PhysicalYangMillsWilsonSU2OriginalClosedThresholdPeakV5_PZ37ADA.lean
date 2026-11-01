import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalThresholdOptimizationV5_PZ37ACZ

/-!
# P4-Q2-PZ37ADA — exact closed-form physical Wilson threshold optimizer

Append-only genuine interacting Wilson SU(2) theorem leaf importing ACZ.
Preserve the original centered Gauss-law direction, original FF receiver,
the actual positive Perron representative, updated transfer section,
two interacting posterior laws and true boundary pair-Haar measure.

For the unchanged physical moments let S>0, B the original finite-volume
receiver FC bound, Wbar>=0 the true higher-Haar residual mean,
tau=(exp(64*b)-1)^2>0, C=tau*B^2>0,
F=4*S/(B^2/2-4*S) in (0,1], and Q=32*S>0.
ACZ's reduced mass-overlap gain is
 Phi(delta)=(Q-delta)*(F-C/(C+delta))-tau*Wbar.

An exact algebraic square-completion, WITHOUT calculus or a surrogate
physical probability space, optimizes the whole interval 0<delta<Q:
 t=sqrt(C*(C+Q)/F), delta_star=t-C.
  g(delta) + F*(C+delta-t)^2/(C+delta) = g(delta_star)
  g(delta_star)=(sqrt(F*(C+Q))-sqrt(C))^2,
where g(delta)=(Q-delta)*(F-C/(C+delta)).
Because the original ACK covariance FC theorem ensures F<=1,
the optimizer is interior exactly when F>C/(C+Q). If this numerical
dominance fails, the entire ACZ moment-based strict positive region test
fails for all 0<delta<Q. When it holds, a single explicit optimized
strict inequality implies the original positive mean GI SQUARED
certificate and, through ACO, an open positive-pair-Haar-mass locus
of nonzero actual signed two-interacting-posterior GI response.

No condition is asserted to hold without proof for the actual Wilson
moments; failure of this sufficient criterion does not prove GI vanishing.
No H-uniform coercivity, continuum 4D reconstruction or mass gap.
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
local instance p4Q2PZ37ADA_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADA_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADA_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADA_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADA_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADA_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" => periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Wbar" => p4Q2PZ37ACK_originalFourModeResidualMoment H
local notation "tau" => p4Q2PZ37ACP_originalPosteriorExponentGapSq
local notation "C" => p4Q2PZ37ACW_originalNegativeFCBudget H
local notation "F" => p4Q2PZ37ACY_originalFourModeMassFloor H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "Phi" => p4Q2PZ37ACZ_reducedThresholdMargin H
local instance p4Q2PZ37ADA_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADA_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Interior maximizer of ACZ's ORIGINAL single-variable threshold
gain, using the true F, C, S at the given original finite-volume link. -/
def p4Q2PZ37ADA_originalClosedOptimalThreshold
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  Real.sqrt (C b hb * (C b hb + 32 * S b hb e) / F b hb e) - C b hb
local notation "Opt" => p4Q2PZ37ADA_originalClosedOptimalThreshold H

/-- Exact optimized ACZ surplus, not a new physical assumption:
 (sqrt(F*(C+32S))-sqrt(C))² - tau*Wbar. -/
def p4Q2PZ37ADA_originalClosedPeakMargin
    (b : ℝ) (hb : 0 ≤ b) (e : Link) : ℝ :=
  (Real.sqrt (F b hb e * (C b hb + 32 * S b hb e)) -
    Real.sqrt (C b hb)) ^ 2 - tau b * Wbar b hb e
local notation "Peak" => p4Q2PZ37ADA_originalClosedPeakMargin H

/-- In positive real parameters, the square-root candidate t has
its exact algebraic squared stationarity relation. -/
theorem p4Q2PZ37ADA_realRoot_pos_sq
    (c f q : ℝ) (hc : 0 < c) (hf : 0 < f) (hq : 0 < q) :
    0 < Real.sqrt (c * (c + q) / f) ∧
      f * (Real.sqrt (c * (c + q) / f)) ^ 2 = c * (c + q) := by
  have hqsum : 0 < c + q := add_pos hc hq
  have harg : 0 < c * (c + q) / f :=
    div_pos (mul_pos hc hqsum) hf
  refine ⟨Real.sqrt_pos.2 harg, ?_⟩
  rw [Real.sq_sqrt harg.le]
  field_simp [ne_of_gt hf]

/-- Exact elementary completion of the square before any physical
substitution, valid even for a noncritical real threshold. -/
theorem p4Q2PZ37ADA_realSquareGapIdentity
    (c f q t delta : ℝ) (hy : 0 < c + delta)
    (hrel : f * t ^ 2 = c * (c + q)) :
    (q - delta) * (f - c / (c + delta)) +
      f * (c + delta - t) ^ 2 / (c + delta) =
      f * (c + q) + c - 2 * f * t := by
  field_simp [ne_of_gt hy]
  nlinarith only [hrel]

/-- The exact completed-square upper height, in nonnegative REAL
square roots, with every positive scalar coefficient retained. -/
theorem p4Q2PZ37ADA_realPeakSquare_eq
    (c f q : ℝ) (hc : 0 < c) (hf : 0 < f) (hq : 0 < q) :
    f * (c + q) + c -
      2 * f * Real.sqrt (c * (c + q) / f) =
      (Real.sqrt (f * (c + q)) - Real.sqrt c) ^ 2 := by
  let t := Real.sqrt (c * (c + q) / f)
  let u := Real.sqrt (f * (c + q))
  let v := Real.sqrt c
  have ht := p4Q2PZ37ADA_realRoot_pos_sq c f q hc hf hq
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = f * (c + q) :=
    Real.sq_sqrt (mul_nonneg hf.le (add_pos hc hq).le)
  have hv2 : v ^ 2 = c := Real.sq_sqrt hc.le
  have hSq : (f * t) ^ 2 = (u * v) ^ 2 := by
    calc
      (f * t) ^ 2 = f * (f * t ^ 2) := by ring
      _ = f * (c * (c + q)) := by rw [ht.2]
      _ = (u * v) ^ 2 := by rw [mul_pow, hu2, hv2]; ring
  have hEq : f * t = u * v := by
    nlinarith only [hSq, mul_nonneg hf.le ht.1.le, mul_nonneg hu hv]
  calc
    f * (c + q) + c -
        2 * f * Real.sqrt (c * (c + q) / f) =
        u ^ 2 + v ^ 2 - 2 * (u * v) := by
          dsimp [t, u, v] at *
          nlinarith only [hu2, hv2, hEq]
    _ = (u - v) ^ 2 := by ring
    _ = (Real.sqrt (f * (c + q)) - Real.sqrt c) ^ 2 := rfl

/-- The closed squared-sqrt expression globally bounds the elementary
ACZ gain at any delta where its original FC denominator is positive. -/
theorem p4Q2PZ37ADA_realGain_le_closedPeak
    (c f q delta : ℝ) (hc : 0 < c) (hf : 0 < f) (hq : 0 < q)
    (hy : 0 < c + delta) :
    (q - delta) * (f - c / (c + delta)) ≤
      (Real.sqrt (f * (c + q)) - Real.sqrt c) ^ 2 := by
  let t := Real.sqrt (c * (c + q) / f)
  have hroot := p4Q2PZ37ADA_realRoot_pos_sq c f q hc hf hq
  have hsq :=
    p4Q2PZ37ADA_realSquareGapIdentity c f q t delta hy hroot.2
  have hnonneg : 0 ≤ f * (c + delta - t) ^ 2 / (c + delta) :=
    div_nonneg (mul_nonneg hf.le (sq_nonneg _)) hy.le
  have hpeak := p4Q2PZ37ADA_realPeakSquare_eq c f q hc hf hq
  dsimp [t] at hsq hnonneg
  linarith only [hsq, hnonneg, hpeak]

/-- At the exact sqrt optimizer, the square gap vanishes and the bound
is attained (whether or not this candidate is physically interior). -/
theorem p4Q2PZ37ADA_realGain_at_closedOptimal
    (c f q : ℝ) (hc : 0 < c) (hf : 0 < f) (hq : 0 < q) :
    (q - (Real.sqrt (c * (c + q) / f) - c)) *
      (f - c / (c + (Real.sqrt (c * (c + q) / f) - c))) =
      (Real.sqrt (f * (c + q)) - Real.sqrt c) ^ 2 := by
  let t := Real.sqrt (c * (c + q) / f)
  have hroot := p4Q2PZ37ADA_realRoot_pos_sq c f q hc hf hq
  have hy : 0 < c + (t - c) := by
    have heq : c + (t - c) = t := by ring
    rw [heq]
    exact hroot.1
  have hzero :
      f * (c + (t - c) - t) ^ 2 / (c + (t - c)) = 0 := by
    have hz : c + (t - c) - t = 0 := by ring
    rw [hz]
    simp
  have hsq :=
    p4Q2PZ37ADA_realSquareGapIdentity c f q t (t - c) hy hroot.2
  rw [hzero, add_zero] at hsq
  have hpeak := p4Q2PZ37ADA_realPeakSquare_eq c f q hc hf hq
  dsimp [t] at hsq
  linarith only [hsq, hpeak]

/-- The exact interior condition for the square-root optimizer when
0<f<=1: the upper-threshold FC ratio must be STRICTLY below f. -/
theorem p4Q2PZ37ADA_realClosedOptimal_interior
    (c f q : ℝ) (hc : 0 < c) (hf : 0 < f) (hq : 0 < q)
    (hfOne : f ≤ 1) (hdom : c / (c + q) < f) :
    0 < Real.sqrt (c * (c + q) / f) - c ∧
      Real.sqrt (c * (c + q) / f) - c < q := by
  let t := Real.sqrt (c * (c + q) / f)
  have hroot := p4Q2PZ37ADA_realRoot_pos_sq c f q hc hf hq
  have harg : 0 ≤ c * (c + q) / f :=
    (div_pos (mul_pos hc (add_pos hc hq)) hf).le
  have ht2 : t ^ 2 = c * (c + q) / f :=
    Real.sq_sqrt harg
  have hmulLe : f * c ^ 2 ≤ c ^ 2 := by
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hfOne (sq_nonneg c))
  have hmulPos := mul_pos hc hq
  have hmulLt : f * c ^ 2 < c * (c + q) := by
    nlinarith only [hmulLe, hmulPos]
  have hrootGtSq : c ^ 2 < t ^ 2 := by
    rw [ht2]
    apply (lt_div_iff₀ hf).mpr
    nlinarith only [hmulLt]
  have hrootGt : c < t := by
    nlinarith only [hrootGtSq, hc, hroot.1]
  have hsum : 0 < c + q := add_pos hc hq
  have hratio : c < f * (c + q) :=
    (div_lt_iff₀ hsum).mp hdom
  have hmulGt := mul_lt_mul_of_pos_right hratio hsum
  have hrootLtSq : t ^ 2 < (c + q) ^ 2 := by
    rw [ht2]
    apply (div_lt_iff₀ hf).mpr
    nlinarith only [hmulGt]
  have hrootLt : t < c + q := by
    nlinarith only [hrootLtSq, hroot.1, hsum]
  exact ⟨by dsimp [t] at hrootGt; linarith only [hrootGt],
    by dsimp [t] at hrootLt; linarith only [hrootLt]⟩

/-- ACK's true original physical FC covariance cap gives a strictly
positive negative-Perron FC budget C=tau*B². -/
theorem p4Q2PZ37ADA_originalNegativeFCBudget_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < C b hb.le := by
  have hs := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b hb e
  have hFC :=
    p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
      H b hb.le e
  have hB : 0 < (B b hb.le) ^ 2 := by
    nlinarith only [hs, hFC]
  change 0 < tau b * (B b hb.le) ^ 2
  exact mul_pos (p4Q2PZ37ACZ_originalPosteriorGap_pos b hb) hB

/-- Original Haar/FC covariance relation implies the genuine ACN
high-four-mode Haar mass floor is at most one, WITHOUT extra assumptions. -/
theorem p4Q2PZ37ADA_originalFourModeFloor_le_one
    (b : ℝ) (hb : 0 < b) (e : Link) :
    F b hb.le e ≤ 1 := by
  have hFC :=
    p4Q2PZ37ACK_originalCovarianceSecondMoment_le_FC_sixteenth
      H b hb.le e
  have hDen :=
    (p4Q2PZ37ACN_highAmplitudeRegion_mass_lower H b hb e).1
  change 4 * S b hb.le e /
    ((B b hb.le) ^ 2 / 2 - 4 * S b hb.le e) ≤ 1
  apply (div_le_iff₀ hDen).mpr
  nlinarith only [hFC]

/-- If the ORIGINAL physical high-four-mode floor exceeds the actual
negative-FC ratio, the exact optimizer is an admissible positive delta. -/
theorem p4Q2PZ37ADA_originalOptimalThreshold_interior
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hdom : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e) :
    0 < Opt b hb.le e ∧ Opt b hb.le e < 32 * S b hb.le e := by
  have hc := p4Q2PZ37ADA_originalNegativeFCBudget_pos H b hb e
  have hf := (p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
    H b hb e).2.1
  have hq := p4Q2PZ37ACZ_originalFourModeThreshold_pos H b hb e
  simpa only [p4Q2PZ37ADA_originalClosedOptimalThreshold] using
    p4Q2PZ37ADA_realClosedOptimal_interior
      (C b hb.le) (F b hb.le e) (32 * S b hb.le e)
      hc hf hq
      (p4Q2PZ37ADA_originalFourModeFloor_le_one H b hb e) hdom

/-- Universal exact square-root ceiling on the original ACZ reduced
margin at every physical positive discriminant threshold delta. -/
theorem p4Q2PZ37ADA_originalReducedMargin_le_closedPeak
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 < delta) :
    Phi b hb.le e delta ≤ Peak b hb.le e := by
  have hc := p4Q2PZ37ADA_originalNegativeFCBudget_pos H b hb e
  have hf := (p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
    H b hb e).2.1
  have hq := p4Q2PZ37ACZ_originalFourModeThreshold_pos H b hb e
  have hbound := p4Q2PZ37ADA_realGain_le_closedPeak
    (C b hb.le) (F b hb.le e) (32 * S b hb.le e) delta
    hc hf hq (add_pos hc hdelta)
  unfold p4Q2PZ37ACZ_reducedThresholdMargin
    p4Q2PZ37ADA_originalClosedPeakMargin
  linarith only [hbound]

/-- Exact attained value of the ORIGINAL reduced margin, without
numerical simulation or replacing the physical higher-Haar mean. -/
theorem p4Q2PZ37ADA_originalReducedMargin_at_closedOptimal
    (b : ℝ) (hb : 0 < b) (e : Link) :
    Phi b hb.le e (Opt b hb.le e) = Peak b hb.le e := by
  have hc := p4Q2PZ37ADA_originalNegativeFCBudget_pos H b hb e
  have hf := (p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
    H b hb e).2.1
  have hq := p4Q2PZ37ACZ_originalFourModeThreshold_pos H b hb e
  have h := p4Q2PZ37ADA_realGain_at_closedOptimal
    (C b hb.le) (F b hb.le e) (32 * S b hb.le e) hc hf hq
  simpa only [p4Q2PZ37ADA_originalClosedOptimalThreshold,
    p4Q2PZ37ACZ_reducedThresholdMargin,
    p4Q2PZ37ADA_originalClosedPeakMargin] using
      congrArg (fun x : ℝ => x - tau b * Wbar b hb.le e) h

/-- A SINGLE closed-form ORIGINAL Wilson moment test suffices for
positive ACO GI SQUARED mean budget, if the optimizer is interior. -/
theorem p4Q2PZ37ADA_originalClosedPeak_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hdom : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e)
    (hpeak : 0 < Peak b hb.le e) :
    0 < Budget b hb.le e := by
  have hin := p4Q2PZ37ADA_originalOptimalThreshold_interior
    H b hb e hdom
  have heq := p4Q2PZ37ADA_originalReducedMargin_at_closedOptimal
    H b hb e
  exact p4Q2PZ37ACZ_reducedMargin_pos_gives_positiveBudget
    H b hb e (Opt b hb.le e) hin.1 hin.2 (heq.symm ▸ hpeak)

/-- Same genuine moment test gives a true nonzero signed
two-interacting-posterior GI response on an OPEN positive-Haar set. -/
theorem p4Q2PZ37ADA_originalClosedPeak_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hdom : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e)
    (hpeak : 0 < Peak b hb.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ADA_originalClosedPeak_gives_positiveBudget
      H b hb e hdom hpeak)

/-- Nonpositive original mean GI squared certificate necessarily
obstructs the STRICT optimized peak at any physically interior optimum. -/
theorem p4Q2PZ37ADA_nonpositiveBudget_closedPeak_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0)
    (hdom : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e) :
    Peak b hb.le e ≤ 0 := by
  have hin := p4Q2PZ37ADA_originalOptimalThreshold_interior
    H b hb e hdom
  have hobs := p4Q2PZ37ACZ_nonpositiveBudget_reducedMargin_obstruction
    H b hb e hNonpos (Opt b hb.le e) hin.1 hin.2
  rw [p4Q2PZ37ADA_originalReducedMargin_at_closedOptimal H b hb e] at hobs
  exact hobs

/-- When F is below the physical endpoint FC ratio, NO positive
delta<32*S can make ACZ's reduced moment criterion positive. -/
theorem p4Q2PZ37ADA_subcriticalRatio_forces_allReduced_nonpositive
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hsub : F b hb.le e ≤
      C b hb.le / (C b hb.le + 32 * S b hb.le e))
    (delta : ℝ) (hdelta : 0 < delta)
    (hInterior : delta < 32 * S b hb.le e) :
    Phi b hb.le e delta ≤ 0 := by
  have hc := p4Q2PZ37ADA_originalNegativeFCBudget_pos H b hb e
  have hq := p4Q2PZ37ACZ_originalFourModeThreshold_pos H b hb e
  have hdenQ : 0 < C b hb.le + 32 * S b hb.le e := add_pos hc hq
  have hdenD : 0 < C b hb.le + delta := add_pos hc hdelta
  have hratio :
      C b hb.le / (C b hb.le + 32 * S b hb.le e) ≤
        C b hb.le / (C b hb.le + delta) := by
    apply (div_le_div_iff₀ hdenQ hdenD).mpr
    nlinarith only [hc.le, hInterior.le]
  have hgain :
      F b hb.le e - C b hb.le / (C b hb.le + delta) ≤ 0 := by
    linarith only [hsub, hratio]
  have hproduct : (32 * S b hb.le e - delta) *
      (F b hb.le e - C b hb.le / (C b hb.le + delta)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hInterior.le) hgain
  have hW := p4Q2PZ37ACK_originalFourModeResidualMoment_nonneg H b hb.le e
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have hrem : 0 ≤ tau b * Wbar b hb.le e := mul_nonneg ht.le hW
  unfold p4Q2PZ37ACZ_reducedThresholdMargin
  linarith only [hproduct, hrem]

/-- Conversely, any positive ACZ reduced margin must surpass the
EXACT physical endpoint ratio. Thus ratio dominance is NECESSARY
for this optimization method, not a guessed Wilson hypothesis. -/
theorem p4Q2PZ37ADA_anyStrictReduced_requires_ratioDominance
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hdelta : 0 < delta)
    (hInterior : delta < 32 * S b hb.le e)
    (hpositive : 0 < Phi b hb.le e delta) :
    C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e := by
  by_contra hn
  have hsub : F b hb.le e ≤
    C b hb.le / (C b hb.le + 32 * S b hb.le e) :=
      le_of_not_gt hn
  have hobs := p4Q2PZ37ADA_subcriticalRatio_forces_allReduced_nonpositive
    H b hb e hsub delta hdelta hInterior
  exact (not_lt_of_ge hobs) hpositive

/-- EXHAUSTIVE iff for the existence of a strict original ACZ
two-threshold moment witness, reduced to one closed physical scalar
comparison plus the exact boundary-ratio feasibility. -/
theorem p4Q2PZ37ADA_exists_strictReduced_iff_closedPeak
    (b : ℝ) (hb : 0 < b) (e : Link) :
    (∃ delta : ℝ, 0 < delta ∧ delta < 32 * S b hb.le e ∧
      0 < Phi b hb.le e delta) ↔
    (C b hb.le / (C b hb.le + 32 * S b hb.le e) <
       F b hb.le e ∧
      0 < Peak b hb.le e) := by
  constructor
  · rintro ⟨delta, hdelta, hinterior, hpositive⟩
    have hdom :=
      p4Q2PZ37ADA_anyStrictReduced_requires_ratioDominance
        H b hb e delta hdelta hinterior hpositive
    have hbound :=
      p4Q2PZ37ADA_originalReducedMargin_le_closedPeak
        H b hb e delta hdelta
    exact ⟨hdom, lt_of_lt_of_le hpositive hbound⟩
  · rintro ⟨hdom, hpeak⟩
    obtain ⟨hdelta, hinterior⟩ :=
      p4Q2PZ37ADA_originalOptimalThreshold_interior H b hb e hdom
    refine ⟨Opt b hb.le e, hdelta, hinterior, ?_⟩
    rw [p4Q2PZ37ADA_originalReducedMargin_at_closedOptimal H b hb e]
    exact hpeak

/-- A viable closed-form optimizer also induces an explicitly positive
physical residual threshold at the SAME original boundary context. -/
theorem p4Q2PZ37ADA_originalClosedOptimalResidual_pos_saturates
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hdom : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e) :
    0 < p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e
      (Opt b hb.le e) ∧
    Opt b hb.le e ≤ 32 * S b hb.le e -
      tau b * p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e
        (Opt b hb.le e) := by
  obtain ⟨hdelta, hinterior⟩ :=
    p4Q2PZ37ADA_originalOptimalThreshold_interior H b hb e hdom
  exact p4Q2PZ37ACZ_maxResidual_pos_and_saturates
    H b hb e (Opt b hb.le e) hdelta hinterior

/-- Any strict original closed-peak moment test entails ACP's exact
true physical exponential residual inequality, not a continuum gap. -/
theorem p4Q2PZ37ADA_closedPeak_implies_exactPhysicalResidualThreshold
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hdom : C b hb.le / (C b hb.le + 32 * S b hb.le e) <
      F b hb.le e)
    (hpeak : 0 < Peak b hb.le e) :
    tau b * Wbar b hb.le e < 64 * S b hb.le e := by
  exact (p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual
    H b hb e).mp
    (p4Q2PZ37ADA_originalClosedPeak_gives_positiveBudget
      H b hb e hdom hpeak)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_realRoot_pos_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_realSquareGapIdentity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_realPeakSquare_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_realGain_le_closedPeak
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_realGain_at_closedOptimal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_realClosedOptimal_interior
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalNegativeFCBudget_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalFourModeFloor_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalOptimalThreshold_interior
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalReducedMargin_le_closedPeak
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalReducedMargin_at_closedOptimal
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalClosedPeak_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalClosedPeak_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_nonpositiveBudget_closedPeak_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_subcriticalRatio_forces_allReduced_nonpositive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_anyStrictReduced_requires_ratioDominance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_exists_strictReduced_iff_closedPeak
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_originalClosedOptimalResidual_pos_saturates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADA_closedPeak_implies_exactPhysicalResidualThreshold
