import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFourModeResidualIntersectionV5_PZ37ACY

/-!
# P4-Q2-PZ37ACZ — physical two-threshold optimization frontier

Append-only theorem leaf on the SAME original finite interacting Wilson SU(2)
physical receiver, positive Perron representative, updated transfer section,
centered Gauss-law source, two actual interacting posteriors, and original
boundary pair-Haar measure.

ACY proved, for r>0 and delta>0 with delta+tau*r<=32*S,
  r*(F-C/(C+delta)) > Wbar ==> M_GI > 0,
where F=4*S/(B^2/2-4*S)>0, C=tau*B^2>=0, tau>0 for b>0.
No physical positivity assumption is inserted.

ACZ reduces these two adjustable thresholds to ONE real delta:
  r_max(delta)=(32*S-delta)/tau.
At every 0<delta<32*S this r_max is positive and saturates the
original four-mode/local Perron threshold constraint. For fixed delta,
it maximizes the certified mass surplus whenever F-C/(C+delta)>=0.
Consequently the original physical sufficient condition is
  (32*S-delta)*(F-C/(C+delta)) > tau*Wbar.
Its contrapositive obstruction is formally preserved. The midpoint
delta=16*S gives a fully explicit non-optimized rational test.

Separately, ACY's *unconditional* selected high-four-mode/low-residual
Haar mass floor at Rcap=B^2-8*S yields a moment-free physical FC
sufficiency test at delta=32*S-tau*Rcap. This requires verifying the
stated two explicit strict inequalities; no Wilson-model sign is claimed.

All statements retain the original exact finite-volume Wilson data.
No volume-uniform coercivity, unproved GI sign, or continuum 4D gap.
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
local instance p4Q2PZ37ACZ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ACZ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ACZ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ACZ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ACZ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ACZ_probability : IsProbabilityMeasure μ :=
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
local notation "Rcap" => p4Q2PZ37ACY_originalSelectedResidualCeiling H
local notation "T" => p4Q2PZ37ACW_originalPositiveWeightThresholdRegion H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local instance p4Q2PZ37ACZ_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ACZ_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The maximal residual threshold compatible with the unchanged
Perron-local inclusion at a prescribed delta. tau is strictly positive
for positive physical coupling. -/
def p4Q2PZ37ACZ_maxResidualAtThreshold
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (delta : ℝ) : ℝ :=
  (32 * S b hb e - delta) / tau b

/-- Purely original-data one-variable margin: its positivity suffices
for the original GI squared mean certificate, but is not asserted. -/
def p4Q2PZ37ACZ_reducedThresholdMargin
    (b : ℝ) (hb : 0 ≤ b) (e : Link) (delta : ℝ) : ℝ :=
  (32 * S b hb e - delta) *
      (F b hb e - C b hb / (C b hb + delta)) -
    tau b * Wbar b hb e

/-- The genuine squared posterior exponential gap is strictly positive
at strictly positive original Wilson coupling. -/
theorem p4Q2PZ37ACZ_originalPosteriorGap_pos
    (b : ℝ) (hb : 0 < b) :
    0 < tau b :=
  p4Q2PZ37ACP_originalPosteriorExponentGapSq_pos b hb

/-- True first-four covariance energy gives a positive original
four-mode threshold budget at each H,b>0 and physical link e. -/
theorem p4Q2PZ37ACZ_originalFourModeThreshold_pos
    (b : ℝ) (hb : 0 < b) (e : Link) :
    0 < 32 * S b hb.le e := by
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b hb e
  linarith only [hS]

/-- Every interior delta selects a positive residual threshold and
SATURATES delta+tau*r<=32*S on the true original receiver. -/
theorem p4Q2PZ37ACZ_maxResidual_pos_and_saturates
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (_hDelta : 0 < delta) (hInterior : delta < 32 * S b hb.le e) :
    0 < p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta ∧
      delta ≤ 32 * S b hb.le e -
        tau b * p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta := by
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have hr : 0 < p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta :=
    div_pos (sub_pos.mpr hInterior) ht
  have hScale :
      tau b * p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta =
        32 * S b hb.le e - delta := by
    unfold p4Q2PZ37ACZ_maxResidualAtThreshold
    field_simp [ne_of_gt ht] <;> ring
  refine ⟨hr, ?_⟩
  rw [hScale]
  linarith

/-- No admissible original residual threshold can exceed r_max(delta).
This is an EXACT optimization of r at each fixed discriminant delta. -/
theorem p4Q2PZ37ACZ_everyAdmissibleResidual_le_max
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r delta : ℝ)
    (hLocal : delta ≤ 32 * S b hb.le e - tau b * r) :
    r ≤ p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta := by
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  unfold p4Q2PZ37ACZ_maxResidualAtThreshold
  apply (le_div_iff₀ ht).mpr
  linarith only [hLocal]

/-- For a fixed delta with nonnegative physical mass-ratio gain,
the saturating r_max is optimal for ACY's linear moment surplus. -/
theorem p4Q2PZ37ACZ_fixedDelta_optimalResidualGain
    (b : ℝ) (hb : 0 < b) (e : Link)
    (r delta : ℝ)
    (hLocal : delta ≤ 32 * S b hb.le e - tau b * r)
    (hGain : 0 ≤ F b hb.le e -
      C b hb.le / (C b hb.le + delta)) :
    r * (F b hb.le e - C b hb.le / (C b hb.le + delta)) ≤
      p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta *
        (F b hb.le e - C b hb.le / (C b hb.le + delta)) := by
  exact mul_le_mul_of_nonneg_right
    (p4Q2PZ37ACZ_everyAdmissibleResidual_le_max
      H b hb e r delta hLocal) hGain

/-- The single-variable physical test is precisely a sufficient ACY
moment-intersection criterion at its largest admissible residual r.
No inequality on the true physical data is presumed. -/
theorem p4Q2PZ37ACZ_reducedMargin_pos_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 < delta) (hInterior : delta < 32 * S b hb.le e)
    (hReduced : 0 < p4Q2PZ37ACZ_reducedThresholdMargin H b hb.le e delta) :
    0 < Budget b hb.le e := by
  let r := p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta
  have hRes :=
    p4Q2PZ37ACZ_maxResidual_pos_and_saturates H b hb e delta hDelta hInterior
  have hr : 0 < r := hRes.1
  have hLocal : delta ≤ 32 * S b hb.le e - tau b * r := hRes.2
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have hScale : tau b * r = 32 * S b hb.le e - delta := by
    dsimp [r, p4Q2PZ37ACZ_maxResidualAtThreshold]
    field_simp [ne_of_gt ht] <;> ring
  have hProd : 0 < tau b *
      (r * (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
        Wbar b hb.le e) := by
    calc
      tau b * (r * (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
          Wbar b hb.le e) =
        (tau b * r) * (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
          tau b * Wbar b hb.le e := by ring
      _ = (32 * S b hb.le e - delta) *
          (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
          tau b * Wbar b hb.le e := by rw [hScale]
      _ > 0 := hReduced
  have hDiff : 0 < r *
      (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
        Wbar b hb.le e :=
    (mul_pos_iff_of_pos_left ht).mp hProd
  have hSurplus :
      r * (C b hb.le / (C b hb.le + delta)) <
        r * F b hb.le e - Wbar b hb.le e := by
    nlinarith only [hDiff]
  exact p4Q2PZ37ACY_originalMomentIntersection_surplus_gives_positiveBudget
    H b hb e r delta hr hDelta hLocal hSurplus

/-- The same optimized ORIGINAL-data test yields a genuine open
positive-Haar-mass region of nonzero signed two-posterior GI response,
via the existing ACO bridge; squared mean and signed GI stay distinct. -/
theorem p4Q2PZ37ACZ_reducedMargin_pos_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 < delta) (hInterior : delta < 32 * S b hb.le e)
    (hReduced : 0 < p4Q2PZ37ACZ_reducedThresholdMargin H b hb.le e delta) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ACZ_reducedMargin_pos_gives_positiveBudget
      H b hb e delta hDelta hInterior hReduced)

/-- If the original mean GI squared certificate is nonpositive, no
interior delta can make the ONE-VARIABLE optimized ACY test positive.
This is an obstruction to this certificate, not GI vanishing. -/
theorem p4Q2PZ37ACZ_nonpositiveBudget_reducedMargin_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0)
    (delta : ℝ) (hDelta : 0 < delta)
    (hInterior : delta < 32 * S b hb.le e) :
    p4Q2PZ37ACZ_reducedThresholdMargin H b hb.le e delta ≤ 0 := by
  let r := p4Q2PZ37ACZ_maxResidualAtThreshold H b hb.le e delta
  have hRes :=
    p4Q2PZ37ACZ_maxResidual_pos_and_saturates H b hb e delta hDelta hInterior
  have hr : 0 < r := hRes.1
  have hLocal : delta ≤ 32 * S b hb.le e - tau b * r := hRes.2
  have ht := p4Q2PZ37ACZ_originalPosteriorGap_pos b hb
  have hScale : tau b * r = 32 * S b hb.le e - delta := by
    dsimp [r, p4Q2PZ37ACZ_maxResidualAtThreshold]
    field_simp [ne_of_gt ht] <;> ring
  have hObs :=
    p4Q2PZ37ACY_nonpositiveBudget_forces_intersectionMomentObstruction
      H b hb e hNonpos r delta hr hDelta hLocal
  have hDiff : r *
      (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
        Wbar b hb.le e ≤ 0 := by
    nlinarith only [hObs]
  unfold p4Q2PZ37ACZ_reducedThresholdMargin
  calc
    (32 * S b hb.le e - delta) *
        (F b hb.le e - C b hb.le / (C b hb.le + delta)) -
        tau b * Wbar b hb.le e =
      tau b * (r * (F b hb.le e -
        C b hb.le / (C b hb.le + delta)) - Wbar b hb.le e) := by
          rw [← hScale]
          ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hDiff

/-- A simple fully explicit physical rational witness at the midpoint
delta=16*S, r=16*S/tau. This is intentionally a checkable SUFFICIENT
test, not a claim of its truth in the interacting Wilson model. -/
theorem p4Q2PZ37ACZ_midpointMomentTest_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hMid :
      tau b * Wbar b hb.le e <
        (16 * S b hb.le e) *
          (F b hb.le e -
            C b hb.le / (C b hb.le + 16 * S b hb.le e))) :
    0 < Budget b hb.le e := by
  have hS := p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment_pos
    H b hb e
  apply p4Q2PZ37ACZ_reducedMargin_pos_gives_positiveBudget
    H b hb e (16 * S b hb.le e)
  · nlinarith only [hS]
  · nlinarith only [hS]
  · unfold p4Q2PZ37ACZ_reducedThresholdMargin
    nlinarith only [hMid]

/-- Any strict positive optimized reduced margin entails this necessary
coarse original four-mode-vs-Haar moment relation. The converse is NOT
claimed, because the genuine threshold-region ratio has a cost. -/
theorem p4Q2PZ37ACZ_reducedMargin_pos_requires_coarseMoment
    (b : ℝ) (hb : 0 < b) (e : Link)
    (delta : ℝ) (hDelta : 0 < delta)
    (hInterior : delta < 32 * S b hb.le e)
    (hReduced : 0 < p4Q2PZ37ACZ_reducedThresholdMargin H b hb.le e delta) :
    tau b * Wbar b hb.le e <
      (32 * S b hb.le e) * F b hb.le e := by
  have hC := p4Q2PZ37ACW_originalNegativeFCBudget_nonneg H b hb.le
  have hDen : 0 < C b hb.le + delta := by linarith only [hC, hDelta]
  have hRatio : 0 ≤ C b hb.le / (C b hb.le + delta) :=
    div_nonneg hC hDen.le
  have hF := (p4Q2PZ37ACY_selectedResidualCeiling_pos_and_highMass
    H b hb e).2.1
  have hNonneg1 :
      0 ≤ (32 * S b hb.le e - delta) *
        (C b hb.le / (C b hb.le + delta)) :=
    mul_nonneg (sub_nonneg.mpr hInterior.le) hRatio
  have hNonneg2 : 0 ≤ delta * F b hb.le e :=
    mul_nonneg hDelta.le hF.le
  unfold p4Q2PZ37ACZ_reducedThresholdMargin at hReduced
  nlinarith only [hReduced, hNonneg1, hNonneg2]

/-- A PHYSICALLY SELECTED no-Wbar-inequality alternative: use ACY's
unconditional high-four-mode Haar floor, already located within the
low-higher-mode region at Rcap. Only two explicit original-data strict
tests are assumed; both are currently open in the actual Wilson model. -/
theorem p4Q2PZ37ACZ_selectedFC_test_gives_positiveBudget
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hDelta :
      0 < 32 * S b hb.le e - tau b * Rcap b hb.le e)
    (hRatio :
      C b hb.le /
        (C b hb.le +
          (32 * S b hb.le e - tau b * Rcap b hb.le e)) <
        F b hb.le e) :
    0 < Budget b hb.le e := by
  have hFloor :=
    (p4Q2PZ37ACY_selectedThreshold_open_positiveHaarMass H b hb e).2.2
  exact p4Q2PZ37ACW_originalRegionMass_ratio_gives_positiveBudget
    H b hb e
    (32 * S b hb.le e - tau b * Rcap b hb.le e) hDelta
    (lt_of_lt_of_le hRatio hFloor)

/-- The same original FC-selected threshold controls a genuinely
nonzero signed two-posterior Wilson response on an open positive-mass
set, conditional on the two concrete numerical FC inequalities. -/
theorem p4Q2PZ37ACZ_selectedFC_test_gives_openGIRegion
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hDelta :
      0 < 32 * S b hb.le e - tau b * Rcap b hb.le e)
    (hRatio :
      C b hb.le /
        (C b hb.le +
          (32 * S b hb.le e - tau b * Rcap b hb.le e)) <
        F b hb.le e) :
    ∃ Uset : Set Pair, IsOpen Uset ∧
      0 < Measure.real outer Uset ∧
      ∀ z ∈ Uset,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b hb.le f₀ e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b hb.le e
    (p4Q2PZ37ACZ_selectedFC_test_gives_positiveBudget
      H b hb e hDelta hRatio)

/-- Necessary obstruction at the physically selected FC threshold if
the true original squared GI mean certificate is nonpositive. -/
theorem p4Q2PZ37ACZ_nonpositiveBudget_selectedFC_obstruction
    (b : ℝ) (hb : 0 < b) (e : Link)
    (hNonpos : Budget b hb.le e ≤ 0)
    (hDelta :
      0 < 32 * S b hb.le e - tau b * Rcap b hb.le e) :
    F b hb.le e ≤
      C b hb.le /
        (C b hb.le +
          (32 * S b hb.le e - tau b * Rcap b hb.le e)) := by
  have hFloor :=
    (p4Q2PZ37ACY_selectedThreshold_open_positiveHaarMass H b hb e).2.2
  have hUpper :=
    p4Q2PZ37ACX_nonpositiveBudget_thresholdMass_upper
      H b hb e
      (32 * S b hb.le e - tau b * Rcap b hb.le e) hDelta hNonpos
  exact hFloor.trans hUpper

/-- Preserve ACP's EXACT physical obstruction boundary: any positive
ACZ optimized sufficient condition implies tau*Wbar<64*S; ACZ does
not prove this strict inequality for the actual interacting data. -/
theorem p4Q2PZ37ACZ_reducedMargin_implies_exactPhysicalThreshold
    (b : ℝ) (hb : 0 < b) (e : Link) (delta : ℝ)
    (hDelta : 0 < delta) (hInterior : delta < 32 * S b hb.le e)
    (hReduced : 0 < p4Q2PZ37ACZ_reducedThresholdMargin H b hb.le e delta) :
    tau b * Wbar b hb.le e < 64 * S b hb.le e := by
  exact (p4Q2PZ37ACP_originalGIMeanBudget_pos_iff_exponential_residual
    H b hb e).mp
      (p4Q2PZ37ACZ_reducedMargin_pos_gives_positiveBudget
        H b hb e delta hDelta hInterior hReduced)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_originalPosteriorGap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_originalFourModeThreshold_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_maxResidual_pos_and_saturates
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_everyAdmissibleResidual_le_max
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_fixedDelta_optimalResidualGain
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_reducedMargin_pos_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_reducedMargin_pos_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_nonpositiveBudget_reducedMargin_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_midpointMomentTest_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_reducedMargin_pos_requires_coarseMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_selectedFC_test_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_selectedFC_test_gives_openGIRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_nonpositiveBudget_selectedFC_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ACZ_reducedMargin_implies_exactPhysicalThreshold
