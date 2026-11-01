import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformTwoSignCovarianceV5_PZ37ADG
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADH — actual Wilson covariance witnesses in positive-Haar metric balls

The original finite interacting Wilson SU(2), centered Gauss-law physical
source, original FF receiver, Perron/transfer section, two interacting
posteriors, and original boundary pair-Haar law are unchanged.

ACI supplies a nonzero physical covariance at some actual boundary pair.
ACD proves its continuity in the original boundary topology; original
pair-Haar has full support. We use a compatible pseudometric presentation
of that SAME topology to enclose a nonzero covariance witness in an OPEN
positive-radius metric ball, carrying POSITIVE ORIGINAL pair-Haar mass.
ADE's exact original covariance-square integral then gives

  (|C_e(z0)|/2)^2 * ν_H(ball(z0,r)) <= S(H,b0,e).

At each fixed finite H with nonempty genuine link type, FINITENESS
produces a common positive radius r_H, amplitude a_H, and ball Haar
mass m_H, while the actual ball centers vary by physical link. Thus
S(H,b0,e) >= a_H^2*m_H for all genuine links, unconditionally.

The extra quantitative condition K_H < 272*a_H^2*m_H remains
UNPROVED. Under it, ADF yields positive original GI SQUARED mean
certificates and open positive-Haar nonzero SIGNED two-posterior GI
response on all links of the fixed volume.

A separate conditional physical Lipschitz modulus L provides an
EXPLICIT possible radius |C_e(z0)|/(2L) and numerical criterion
K_H < 68*C_e(z0)^2*ν_H(ball). No physical Lipschitz constant or
numerical ball Haar mass is invented or asserted.

The chosen pseudometric is compatible with the existing topology,
not a replacement physical probability law or an independently
calibrated lattice distance. Neither a numerical H-uniform bound
nor the continuum four-dimensional Yang--Mills mass gap follows.
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
local instance p4Q2PZ37ADH_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADH_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADH_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADH_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADH_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADH_probability : IsProbabilityMeasure μ :=
  normalizedCompactHaar_isProbabilityMeasure G

local instance p4Q2PZ37ADH_matrixPseudometrizable :
    TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℂ) := by
  change TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ)
  infer_instance

local instance p4Q2PZ37ADH_groupPseudometrizable :
    TopologicalSpace.PseudoMetrizableSpace G := by
  change TopologicalSpace.PseudoMetrizableSpace
    {u : Matrix (Fin 2) (Fin 2) ℂ |
      u ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ}
  infer_instance

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
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "K" => p4Q2PZ37ADF_originalTransferPlaquetteFCBound H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local instance p4Q2PZ37ADH_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADH_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ADH_pairPseudometrizable :
    TopologicalSpace.PseudoMetrizableSpace Pair := by
  infer_instance
local instance p4Q2PZ37ADH_pairPseudoMetric : PseudoMetricSpace Pair :=
  TopologicalSpace.pseudoMetrizableSpacePseudoMetric _

private theorem p4Q2PZ37ADH_originalOuterOpenPos :
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2).IsOpenPosMeasure := by
    unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
    infer_instance
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- An open metric ball for the SAME original pair topology has strictly
positive original pair-Haar REAL mass for each positive radius. -/
theorem p4Q2PZ37ADH_originalBallHaarMass_pos
    (z₀ : Pair) (r : ℝ) (hr : 0 < r) :
    0 < Measure.real outer (Metric.ball z₀ r) := by
  letI : (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2).IsOpenPosMeasure :=
    p4Q2PZ37ADH_originalOuterOpenPos H
  have hBall : (Metric.ball z₀ r).Nonempty :=
    ⟨z₀, Metric.mem_ball_self hr⟩
  exact ENNReal.toReal_pos
    ((Metric.isOpen_ball).measure_pos outer hBall).ne'
      (measure_ne_top _ _)

/-- At an ACTUAL nonzero original centered-source covariance point, true
boundary continuity yields a positive-radius ball with HALF of the
real physical covariance amplitude on EVERY point of this ball. -/
theorem p4Q2PZ37ADH_originalNonzeroCovariance_existsBall
    (e : Link) (z₀ : Pair)
    (hz₀ : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.ball z₀ r,
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2 ≤
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
  have hCont : Continuous (fun z : Pair =>
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) :=
    p4Q2PZ37ACD_originalReceiver_covariance_continuous
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e
  let a : ℝ :=
    |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2
  let U : Set Pair := {z | a < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|}
  have hOpen : IsOpen U := isOpen_lt continuous_const hCont.abs
  have hAt : z₀ ∈ U := by
    change a < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀|
    dsimp [a]
    have hPos :
        0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| :=
      abs_pos.mpr hz₀
    linarith
  obtain ⟨r, hr, hSubset⟩ := (Metric.isOpen_iff.1 hOpen) z₀ hAt
  refine ⟨r, hr, ?_⟩
  intro z hz
  exact (hSubset hz).le

/-- Original Haar mass and the EXACT covariance-square moment are
simultaneously bounded from below by one physical covariance ball. -/
theorem p4Q2PZ37ADH_originalNonzeroCovariance_ballMomentWitness
    (e : Link) (z₀ : Pair)
    (hz₀ : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      0 < Measure.real outer (Metric.ball z₀ r) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2) ^ 2 *
        Measure.real outer (Metric.ball z₀ r) ≤
          S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨r, hr, hCov⟩ :=
    p4Q2PZ37ADH_originalNonzeroCovariance_existsBall H e z₀ hz₀
  have ha :
      0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2 :=
    div_pos (abs_pos.mpr hz₀) (by norm_num)
  refine ⟨r, hr, p4Q2PZ37ADH_originalBallHaarMass_pos H z₀ r hr, ?_⟩
  exact p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
    H e (Metric.ball z₀ r)
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2)
      Metric.isOpen_ball ha hCov

/-- ACI's original interacting Wilson covariance witnesses remove
the nonzero-point hypothesis, without postulating any replacement law.
Every physical link has a true nonzero-point Haar-ball moment witness. -/
theorem p4Q2PZ37ADH_originalEveryLink_ballMomentWitness
    (e : Link) :
    ∃ (z₀ : Pair) (r : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0 ∧
      0 < r ∧ 0 < Measure.real outer (Metric.ball z₀ r) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2) ^ 2 *
        Measure.real outer (Metric.ball z₀ r) ≤
          S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨z₀, hz₀⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  obtain ⟨r, hr, hMass, hMoment⟩ :=
    p4Q2PZ37ADH_originalNonzeroCovariance_ballMomentWitness H e z₀ hz₀
  exact ⟨z₀, r, hz₀, hr, hMass, hMoment⟩

/-- In a fixed H with finitely many ORIGINAL physical links one can
choose one radius r>0, one covariance amplitude a>0 and one actual
pair-Haar ball mass m>0 for ALL links simultaneously.
The physical center z_e varies with e; only the three real constants
are common. They are H-dependent, not claimed numerical or uniform in H. -/
theorem p4Q2PZ37ADH_fixedVolume_commonPhysicalHaarBalls
    [Nonempty Link] :
    ∃ r a m : ℝ, 0 < r ∧ 0 < a ∧ 0 < m ∧
      ∀ e : Link, ∃ z₀ : Pair,
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0 ∧
        m ≤ Measure.real outer (Metric.ball z₀ r) ∧
        (∀ z ∈ Metric.ball z₀ r,
          a ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) := by
  classical
  have hPoints : ∀ e : Link, ∃ z₀ : Pair,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0 := by
    intro e
    exact p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  choose z₀ hz₀ using hPoints
  have hRadii : ∀ e : Link, ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ Metric.ball (z₀ e) r,
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e (z₀ e)| / 2 ≤
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) := by
    intro e
    exact p4Q2PZ37ADH_originalNonzeroCovariance_existsBall
      H e (z₀ e) (hz₀ e)
  choose radius hRadius hCov using hRadii
  obtain ⟨eR, _, hMinR⟩ :=
    Set.exists_min_image (Set.univ : Set Link)
      (fun e : Link => radius e)
      (Set.finite_univ : (Set.univ : Set Link).Finite)
      (Set.univ_nonempty : (Set.univ : Set Link).Nonempty)
  let r₀ : ℝ := radius eR
  have hr₀ : 0 < r₀ := hRadius eR
  let amp : Link → ℝ :=
    fun e => |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e (z₀ e)| / 2
  have hAmp : ∀ e : Link, 0 < amp e := by
    intro e
    exact div_pos (abs_pos.mpr (hz₀ e)) (by norm_num)
  obtain ⟨eA, _, hMinA⟩ :=
    Set.exists_min_image (Set.univ : Set Link)
      (fun e : Link => amp e)
      (Set.finite_univ : (Set.univ : Set Link).Finite)
      (Set.univ_nonempty : (Set.univ : Set Link).Nonempty)
  let mass : Link → ℝ :=
    fun e => Measure.real outer (Metric.ball (z₀ e) r₀)
  have hMass : ∀ e : Link, 0 < mass e := by
    intro e
    exact p4Q2PZ37ADH_originalBallHaarMass_pos H (z₀ e) r₀ hr₀
  obtain ⟨eM, _, hMinM⟩ :=
    Set.exists_min_image (Set.univ : Set Link)
      (fun e : Link => mass e)
      (Set.finite_univ : (Set.univ : Set Link).Finite)
      (Set.univ_nonempty : (Set.univ : Set Link).Nonempty)
  refine ⟨r₀, amp eA, mass eM, hr₀, hAmp eA, hMass eM, ?_⟩
  intro e
  refine ⟨z₀ e, hz₀ e, hMinM e (Set.mem_univ e), ?_⟩
  intro z hz
  have hWide : z ∈ Metric.ball (z₀ e) (radius e) :=
    Metric.ball_subset_ball (hMinR e (Set.mem_univ e)) hz
  exact (hMinA e (Set.mem_univ e)).trans (hCov e z hWide)

/-- The FIXED-H physical Haar balls, rather than abstract nonempty
OPEN regions, give a uniform positive actual covariance-square moment
floor for every link, with original pair-Haar integration unchanged. -/
theorem p4Q2PZ37ADH_fixedVolume_commonBallMomentLower
    [Nonempty Link] :
    ∃ r a m : ℝ, 0 < r ∧ 0 < a ∧ 0 < m ∧
      ∀ e : Link,
        a ^ 2 * m ≤ S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨r, a, m, hr, ha, hm, hBalls⟩ :=
    p4Q2PZ37ADH_fixedVolume_commonPhysicalHaarBalls H
  refine ⟨r, a, m, hr, ha, hm, ?_⟩
  intro e
  obtain ⟨z₀, _, hMass, hCov⟩ := hBalls e
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Metric.ball z₀ r) a Metric.isOpen_ball ha hCov
  exact (mul_le_mul_of_nonneg_left hMass (sq_nonneg a)).trans hMoment

/-- Conditional exact GI certificate on every original link of a
fixed H, using genuine measured metric balls. The new strict
inequality K_H<272*a²*m is an explicit numerical OBLIGATION,
not a consequence of positive r,a,m. -/
theorem p4Q2PZ37ADH_fixedVolume_ballNumericGivesAllGI
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
  exact p4Q2PZ37ADG_originalPhysicalRegion_numericGivesAllGI
    H a m hFloor hNumeric

/-- An externally certified Lipschitz constant L for the ACTUAL
original covariance, if established, yields the EXPLICIT radius
|C(z0)|/(2L). This theorem does NOT assert such a constant is
already known or physically H-uniform. -/
theorem p4Q2PZ37ADH_originalLipschitz_gives_explicitBall
    (e : Link) (z₀ : Pair)
    (hz₀ : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z : Pair,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| ≤
          L * dist z z₀) :
    0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L) ∧
      ∀ z ∈ Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)),
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2 ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
  have hr :
      0 < |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L) :=
    div_pos (abs_pos.mpr hz₀) (mul_pos (by norm_num) hL)
  refine ⟨hr, ?_⟩
  intro z hz
  have hDist :
      L * dist z z₀ <
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2 := by
    have h := mul_lt_mul_of_pos_left (Metric.mem_ball.mp hz) hL
    have hEq :
        L * (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)) =
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2 := by
      field_simp [ne_of_gt hL]
    exact lt_of_lt_of_eq h hEq
  have hTriangle :
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| +
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
    calc
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| =
          |(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ -
            C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) +
            C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
          congr 1
          ring
      _ ≤ |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ -
            C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| +
            |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := abs_add_le _ _
      _ = |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
            C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| +
            |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
        rw [abs_sub_comm]
  have hl := hLip z
  linarith only [hTriangle, hl, hDist]

/-- A certified genuine covariance Lipschitz bound leads to an
explicit-radius ball of positive actual Haar mass, and to an exact
moment lower bound using the ORIGINAL Wilson receiver. -/
theorem p4Q2PZ37ADH_originalLipschitzBall_momentLower
    (e : Link) (z₀ : Pair)
    (hz₀ : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z : Pair,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| ≤
          L * dist z z₀) :
    0 < Measure.real outer (Metric.ball z₀
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L))) ∧
    (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L))) ≤
      S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨hr, hBall⟩ :=
    p4Q2PZ37ADH_originalLipschitz_gives_explicitBall
      H e z₀ hz₀ L hL hLip
  exact ⟨p4Q2PZ37ADH_originalBallHaarMass_pos H z₀ _ hr,
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)))
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2)
        Metric.isOpen_ball
        (div_pos (abs_pos.mpr hz₀) (by norm_num)) hBall⟩

/-- The missing original-model numeric comparison is now localized
to ONE actual nonzero covariance point and the mass of ONE actual
boundary Haar ball, at the explicit conditional radius |C(z0)|/(2L).
The coefficient 68 is EXACT: 272*(|C(z0)|/2)^2=68*C(z0)^2.
No asserted Lipschitz constant or ball mass is manufactured. -/
theorem p4Q2PZ37ADH_originalLipschitzBall_numericGivesGI
    (e : Link) (z₀ : Pair)
    (hz₀ : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀ ≠ 0)
    (L : ℝ) (hL : 0 < L)
    (hLip : ∀ z : Pair,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| ≤
          L * dist z z₀)
    (hNumeric : K <
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)))) :
    0 < Budget b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e ∧
      ∃ V : Set Pair, IsOpen V ∧ 0 < Measure.real outer V ∧
        ∀ z ∈ V,
          0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
            H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e z| := by
  obtain ⟨_, hBall⟩ :=
    p4Q2PZ37ADH_originalLipschitz_gives_explicitBall
      H e z₀ hz₀ L hL hLip
  have ha : 0 <
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2 :=
    div_pos (abs_pos.mpr hz₀) (by norm_num)
  have hScale :
      272 * ((|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)))) =
      68 * (C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L))) := by
    rw [div_pow, sq_abs]
    ring
  have hRegionNumerical : K <
      272 * ((|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2) ^ 2 *
        Measure.real outer (Metric.ball z₀
          (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)))) := by
    rw [hScale]
    exact hNumeric
  exact ⟨p4Q2PZ37ADF_transferPlaquetteBound_lt_region_gives_positiveBudget
      H e (Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)))
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2)
        Metric.isOpen_ball ha hBall hRegionNumerical,
    p4Q2PZ37ADF_transferPlaquetteBound_lt_region_gives_openGI
      H e (Metric.ball z₀
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / (2 * L)))
        (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z₀| / 2)
        Metric.isOpen_ball ha hBall hRegionNumerical⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalBallHaarMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalNonzeroCovariance_existsBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalNonzeroCovariance_ballMomentWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalEveryLink_ballMomentWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_fixedVolume_commonPhysicalHaarBalls
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_fixedVolume_commonBallMomentLower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_fixedVolume_ballNumericGivesAllGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalLipschitz_gives_explicitBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalLipschitzBall_momentLower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADH_originalLipschitzBall_numericGivesGI
