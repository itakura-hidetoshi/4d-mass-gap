import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTransferPlaquetteFCBoundV5_PZ37ADF

/-!
# P4-Q2-PZ37ADG — one fixed-volume lower amplitude and Haar mass for every physical link

The SAME genuinely interacting finite-volume Wilson SU(2) model, the
centered Gauss-law source, original FF receiver, Perron representative,
original transfer and two interacting posteriors, and original boundary
pair-Haar measure are retained.

For a fixed H with nonempty original link type, ADE gives a genuine
finite-link common covariance-moment lower bound s_H>0. ACJ gives
OPEN positive and negative covariance regions at each original link
with Haar mass at least S_e/(B_H^2-2*S_e)>0. ADF proves the
explicit original transfer/plaquette cap B_H^2<=K_H.

The NEW one-volume common tail parameters are

   a_H = sqrt(s_H/2)>0,
   m_H = s_H/(K_H-2*s_H)>0.

On BOTH actual ACJ sign regions for EVERY physical link e,
the covariance has the indicated magnitude at least a_H and each
region's original pair-Haar mass is at least m_H. This is a
nontrivial simultaneous positive/negative Haar region certificate,
without any substitute Gibbs or independent Haar model and without
claiming a positive volume-uniform lower bound.

An additional independent numerical test K_H<272*a_H^2*m_H
implies the TRUE original GI squared mean certificate is positive
and a nonzero signed two-interacting-posterior GI response exists
on an OPEN positive-pair-Haar-mass region, for EVERY link of this H.

We do NOT prove that additional strict test for the genuine Wilson
model, or any bound uniform in H, or a continuum Yang--Mills gap.
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
local instance p4Q2PZ37ADG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADG_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADG_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADG_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADG_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADG_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "c" => p4Q2PZ37ACJ_originalCovarianceMomentThreshold H
local notation "d" => p4Q2PZ37ACJ_originalCovarianceMomentDefectCap H
local notation "Pos" => p4Q2PZ37ACJ_originalPositiveCovarianceMomentRegion H
local notation "Neg" => p4Q2PZ37ACJ_originalNegativeCovarianceMomentRegion H
local notation "K" => p4Q2PZ37ADF_originalTransferPlaquetteFCBound H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local instance p4Q2PZ37ADG_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADG_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A reusable real inequality: a smaller strictly positive moment,
combined with a larger actual FC cap, yields a smaller positive
two-sided covariance tail-mass lower bound. -/
theorem p4Q2PZ37ADG_realUniformTailMassComparison
    (s t x k : ℝ)
    (hs : 0 < s) (hsS : s ≤ t)
    (hd : 0 < x - 2 * t) (hxk : x ≤ k) :
    0 < k - 2 * s ∧
      s / (k - 2 * s) ≤ t / (x - 2 * t) := by
  have hD : x - 2 * t ≤ k - 2 * s := by linarith
  have hK : 0 < k - 2 * s := lt_of_lt_of_le hd hD
  have hS : 0 ≤ t := (le_of_lt hs).trans hsS
  have hCross : s * (x - 2 * t) ≤ t * (k - 2 * s) := by
    calc
      s * (x - 2 * t) ≤ t * (x - 2 * t) :=
        mul_le_mul_of_nonneg_right hsS hd.le
      _ ≤ t * (k - 2 * s) :=
        mul_le_mul_of_nonneg_left hD hS
  exact ⟨hK, (div_le_div_iff₀ hK hd).2 hCross⟩

/-- Every finite-volume common covariance-moment floor s produces
the SAME explicit amplitude for BOTH original signs. -/
def p4Q2PZ37ADG_originalCommonTailAmplitude (s : ℝ) : ℝ :=
  Real.sqrt (s / 2)

/-- This real Haar-mass threshold uses the ACTUAL transfer/plaquette cap K_H,
not an independent sampling distribution or an invented H-uniform bound. -/
def p4Q2PZ37ADG_originalCommonTailMassFloor (s : ℝ) : ℝ :=
  s / (K - 2 * s)

/-- For EACH actual link and ANY given positive common moment floor s,
both original ACJ covariance sign regions have OPEN topology,
a common positive lower Haar mass, and a common positive lower
covariance amplitude. The mass comparison is an exact consequence
of ACJ, ADE, and ADF on the same original Wilson receiver. -/
theorem p4Q2PZ37ADG_originalTwoSignRegion_uniformFromMomentFloor
    (s : ℝ) (hs : 0 < s)
    (e : Link) (hFloor : s ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    0 < p4Q2PZ37ADG_originalCommonTailAmplitude s ∧
    0 < p4Q2PZ37ADG_originalCommonTailMassFloor H s ∧
    IsOpen (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
    IsOpen (Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
    p4Q2PZ37ADG_originalCommonTailMassFloor H s ≤
      Measure.real outer (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
    p4Q2PZ37ADG_originalCommonTailMassFloor H s ≤
      Measure.real outer (Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
    (∀ z ∈ Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e,
      p4Q2PZ37ADG_originalCommonTailAmplitude s <
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) ∧
    (∀ z ∈ Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e,
      p4Q2PZ37ADG_originalCommonTailAmplitude s <
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)) := by
  obtain ⟨_hc, hd, hMassPos, hMassNeg⟩ :=
    p4Q2PZ37ACJ_originalCovarianceMomentRegions_mass_lower
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
  have hd' :
      0 < (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 -
        2 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
    exact hd
  have hK :
      (B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 ≤ K :=
    p4Q2PZ37ADF_originalFCsq_le_transferPlaquetteBound H
  obtain ⟨hDen, hRatio⟩ :=
    p4Q2PZ37ADG_realUniformTailMassComparison
      s (S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
      ((B b₀ p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2)
      K hs hFloor hd' hK
  have ha : 0 < p4Q2PZ37ADG_originalCommonTailAmplitude s := by
    change 0 < Real.sqrt (s / 2)
    exact Real.sqrt_pos.2 (div_pos hs (by norm_num))
  have hm : 0 < p4Q2PZ37ADG_originalCommonTailMassFloor H s := by
    change 0 < s / (K - 2 * s)
    exact div_pos hs hDen
  have haLe :
      p4Q2PZ37ADG_originalCommonTailAmplitude s ≤
        c b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
    change Real.sqrt (s / 2) ≤
      Real.sqrt (S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e / 2)
    exact Real.sqrt_le_sqrt (by linarith)
  have hOpen :=
    p4Q2PZ37ACJ_originalCovarianceMomentRegions_isOpen
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e
  have hp :
      p4Q2PZ37ADG_originalCommonTailMassFloor H s ≤
        Measure.real outer (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) := by
    change s / (K - 2 * s) ≤
      Measure.real outer (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
    exact hRatio.trans hMassPos
  have hn :
      p4Q2PZ37ADG_originalCommonTailMassFloor H s ≤
        Measure.real outer (Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) := by
    change s / (K - 2 * s) ≤
      Measure.real outer (Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
    exact hRatio.trans hMassNeg
  have hPos (z : Pair)
      (hz : z ∈ Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
      p4Q2PZ37ADG_originalCommonTailAmplitude s <
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z := by
    change c b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e <
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z at hz
    exact lt_of_le_of_lt haLe hz
  have hNeg (z : Pair)
      (hz : z ∈ Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
      p4Q2PZ37ADG_originalCommonTailAmplitude s <
        -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) := by
    change C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z <
      -(c b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) at hz
    linarith
  exact ⟨ha, hm, hOpen.1, hOpen.2, hp, hn, hPos, hNeg⟩

/-- A FIXED finite H with nonempty original physical link set possesses
ONE strictly positive covariance amplitude and ONE strictly positive
pair-Haar mass floor, simultaneously for both signs and every link.
The open sets vary genuinely with the physical link. -/
theorem p4Q2PZ37ADG_fixedVolume_allLinks_twoSignUniformWitness
    [Nonempty Link] :
    ∃ a m : ℝ, 0 < a ∧ 0 < m ∧
      ∀ e : Link,
        IsOpen (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
        IsOpen (Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
        m ≤ Measure.real outer (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
        m ≤ Measure.real outer (Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) ∧
        (∀ z ∈ Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e,
          a < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) ∧
        (∀ z ∈ Neg b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e,
          a < -(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)) := by
  classical
  obtain ⟨s, hs, hFloor⟩ :=
    p4Q2PZ37ADE_fixedVolumePositiveCovarianceMomentConstant H
  let a := p4Q2PZ37ADG_originalCommonTailAmplitude s
  let m := p4Q2PZ37ADG_originalCommonTailMassFloor H s
  let e₀ : Link := Classical.choice inferInstance
  obtain ⟨ha, hm, _, _, _, _, _, _⟩ :=
    p4Q2PZ37ADG_originalTwoSignRegion_uniformFromMomentFloor
      H s hs e₀ (hFloor e₀)
  refine ⟨a, m, ha, hm, ?_⟩
  intro e
  obtain ⟨_, _, hOpenPos, hOpenNeg, hMassPos, hMassNeg, hPos, hNeg⟩ :=
    p4Q2PZ37ADG_originalTwoSignRegion_uniformFromMomentFloor
      H s hs e (hFloor e)
  exact ⟨hOpenPos, hOpenNeg, hMassPos, hMassNeg, hPos, hNeg⟩

/-- Exact dependence of the actual covariance-square moment on
the common positive sign region and its common Haar mass floor.
This uses the original ACJ open sets and ADE's integral comparison. -/
theorem p4Q2PZ37ADG_commonTailWitness_lowerOriginalMoment
    (s : ℝ) (hs : 0 < s) (e : Link)
    (hFloor : s ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
    (p4Q2PZ37ADG_originalCommonTailAmplitude s) ^ 2 *
      p4Q2PZ37ADG_originalCommonTailMassFloor H s ≤
        S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨ha, _, hOpen, _, hm, _, hPos, _⟩ :=
    p4Q2PZ37ADG_originalTwoSignRegion_uniformFromMomentFloor
      H s hs e hFloor
  have hCov (z : Pair)
      (hz : z ∈ Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e) :
      p4Q2PZ37ADG_originalCommonTailAmplitude s ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
    have hp := hPos z hz
    have hcp : 0 < C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z :=
      ha.trans hp
    simpa only [abs_of_pos hcp] using hp.le
  have hActual :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Pos b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
      (p4Q2PZ37ADG_originalCommonTailAmplitude s)
      hOpen ha hCov
  exact (mul_le_mul_of_nonneg_left hm (sq_nonneg _)).trans hActual

/-- A single explicit numerical comparison of the ORIGINAL global
transfer/plaquette cap with the newly constructed uniform two-sided
Haar witness suffices for ALL actual links of a FIXED finite volume.
Neither the numerical comparison nor volume uniformity is asserted. -/
theorem p4Q2PZ37ADG_commonTailNumerical_allLinks_positiveBudget
    [Nonempty Link]
    (s : ℝ) (hs : 0 < s)
    (hFloor : ∀ e : Link,
      s ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
    (hNumeric :
      K < 272 * ((p4Q2PZ37ADG_originalCommonTailAmplitude s) ^ 2 *
        p4Q2PZ37ADG_originalCommonTailMassFloor H s)) :
    ∀ e : Link,
      0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  intro e
  have hMoment :=
    p4Q2PZ37ADG_commonTailWitness_lowerOriginalMoment H s hs e (hFloor e)
  have hNumericMoment :
      K < 272 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e :=
    lt_of_lt_of_le hNumeric
      (mul_le_mul_of_nonneg_left hMoment (by norm_num))
  exact p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_positiveBudget
    H e hNumericMoment

/-- Same original fixed-volume quantitative witness and condition
implies an OPEN region with nonzero SIGNED genuine two-interacting-
posterior GI response at every physical link. -/
theorem p4Q2PZ37ADG_commonTailNumerical_allLinks_openSignedGI
    [Nonempty Link]
    (s : ℝ) (hs : 0 < s)
    (hFloor : ∀ e : Link,
      s ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
    (hNumeric :
      K < 272 * ((p4Q2PZ37ADG_originalCommonTailAmplitude s) ^ 2 *
        p4Q2PZ37ADG_originalCommonTailMassFloor H s)) :
    ∀ e : Link, ∃ V : Set Pair,
      IsOpen V ∧ 0 < Measure.real outer V ∧
      ∀ z ∈ V,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  intro e
  have hMoment :=
    p4Q2PZ37ADG_commonTailWitness_lowerOriginalMoment H s hs e (hFloor e)
  have hNumericMoment :
      K < 272 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e :=
    lt_of_lt_of_le hNumeric
      (mul_le_mul_of_nonneg_left hMoment (by norm_num))
  exact p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_openGI
    H e hNumericMoment


/-- The original ACI/ACD genuinely provide an OPEN covariance region
for each original physical link, with strictly positive amplitude and
original boundary-pair-Haar mass. FINITENESS of the actual link type
allows simultaneous minima of the AMPLITUDES and of the HAAR MASSES,
without first defining or estimating S(H,b0,e). This gives an
independently region-sourced positive finite-volume certificate. -/
theorem p4Q2PZ37ADG_originalPhysicalRegion_commonAmplitudeMass_exists
    [Nonempty Link] :
    ∃ a m : ℝ, 0 < a ∧ 0 < m ∧
      ∀ e : Link, ∃ U : Set Pair,
        IsOpen U ∧ m ≤ Measure.real outer U ∧
        (∀ z ∈ U,
          a ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) := by
  classical
  have hRegions : ∀ e : Link, ∃ a : ℝ, ∃ U : Set Pair,
      0 < a ∧ IsOpen U ∧ 0 < Measure.real outer U ∧
      (∀ z ∈ U,
        a ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) := by
    intro e
    exact p4Q2PZ37ADE_originalPhysicalCovarianceRegion_exists H e
  choose a U ha hOpen hMass hCov using hRegions
  obtain ⟨ea, _, hMinA⟩ :=
    Set.exists_min_image (Set.univ : Set Link)
      (fun e : Link => a e)
      (Set.finite_univ : (Set.univ : Set Link).Finite)
      (Set.univ_nonempty : (Set.univ : Set Link).Nonempty)
  obtain ⟨em, _, hMinM⟩ :=
    Set.exists_min_image (Set.univ : Set Link)
      (fun e : Link => Measure.real outer (U e))
      (Set.finite_univ : (Set.univ : Set Link).Finite)
      (Set.univ_nonempty : (Set.univ : Set Link).Nonempty)
  refine ⟨a ea, Measure.real outer (U em), ha ea, hMass em, ?_⟩
  intro e
  refine ⟨U e, hOpen e, hMinM e (Set.mem_univ e), ?_⟩
  intro z hz
  exact (hMinA e (Set.mem_univ e)).trans (hCov e z hz)

/-- A genuine OPEN-REGION lower bound for the original covariance
second moment, uniform in e for every fixed finite H. Unlike the
tail-mass witness above, its two scalar data are selected directly
from ACI/ACD covariance regions, before invoking S. -/
theorem p4Q2PZ37ADG_originalPhysicalRegion_commonMomentLower_exists
    [Nonempty Link] :
    ∃ a m : ℝ, 0 < a ∧ 0 < m ∧
      ∀ e : Link,
        a ^ 2 * m ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨a, m, ha, hm, hRegion⟩ :=
    p4Q2PZ37ADG_originalPhysicalRegion_commonAmplitudeMass_exists H
  refine ⟨a, m, ha, hm, ?_⟩
  intro e
  obtain ⟨U, hOpen, hMass, hCov⟩ := hRegion e
  have hLocal :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e U a hOpen ha hCov
  exact (mul_le_mul_of_nonneg_left hMass (sq_nonneg a)).trans hLocal

/-- The only remaining extra obligation is a strict comparison of
the explicit ORIGINAL Wilson action/plaquette cap K_H with the real
region-sourced product a_H²*m_H. Under it all original links possess
a positive GI SQUARED mean certificate and a genuinely nonzero SIGNED
two-interacting-posterior response on some OPEN positive-Haar region.
The existence of a_H,m_H alone does NOT establish this inequality. -/
theorem p4Q2PZ37ADG_originalPhysicalRegion_numericGivesAllGI
    [Nonempty Link]
    (a m : ℝ)
    (hFloor : ∀ e : Link,
      a ^ 2 * m ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e)
    (hNumeric : K < 272 * (a ^ 2 * m)) :
    ∀ e : Link,
      0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e ∧
      ∃ V : Set Pair, IsOpen V ∧ 0 < Measure.real outer V ∧
        ∀ z ∈ V,
          0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  intro e
  have hNumericMoment :
      K < 272 * S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e :=
    lt_of_lt_of_le hNumeric
      (mul_le_mul_of_nonneg_left (hFloor e) (by norm_num))
  exact ⟨p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_positiveBudget
      H e hNumericMoment,
    p4Q2PZ37ADF_transferPlaquetteBound_lt_moment_gives_openGI
      H e hNumericMoment⟩


end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_realUniformTailMassComparison
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_originalTwoSignRegion_uniformFromMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_fixedVolume_allLinks_twoSignUniformWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_commonTailWitness_lowerOriginalMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_commonTailNumerical_allLinks_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_commonTailNumerical_allLinks_openSignedGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_originalPhysicalRegion_commonAmplitudeMass_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_originalPhysicalRegion_commonMomentLower_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADG_originalPhysicalRegion_numericGivesAllGI
