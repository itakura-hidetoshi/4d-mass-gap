import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExceptionalHaarTailBudgetV5_PZ37AFA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFB — genuine exceptional pair-Haar finite-net certificate

Continue AFA on the same original interacting Wilson SU(2), centered
Gauss-law physical source, genuine Perron vacuum, updated right-link
transfer and true outer pair-Haar probability law.

The strict AFA exception is the positive set of the actual continuous
residual gap G_theta(z) = W_F(z) - theta * A_F(z)^2.
AEE supplies finite nets in the original calibrated all-link D_H,
and ADM supplies a uniform D_H modulus for this continuous gap.

Given an actual certified net of radius r and a verified gap
oscillation < eta, the exceptional event is contained in the union
of only those net balls whose center fails the guarded sample test

  theta * A_F(a)^2 >= W_F(a) + eta.

Consequently its true Haar mass is at most the sum of true Haar masses
of flagged original D_H balls. A separate certified ball-mass budget
or a per-ball cap makes this an explicit numerical AFA input.

Existence of such a finite cover is unconditional at fixed H, but no
smallness of the flagged union, ball-mass numerical value, explicit
finite net, uniform-in-H estimate, or continuum mass gap is claimed.
The AEX conservative two-ball FC no-go remains unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Any verified finite net and an oscillation certificate for the
actual residual gap cover its entire strict-positive set by precisely
those cells whose samples fail the margin-eta good test. -/
theorem p4Q2PZ37AFB_finiteNetExceptionalCover
    {α : Type*} (s : Finset α) (d : α → α → ℝ)
    (r theta eta : ℝ) (f g : α → ℝ)
    (hNet : ∀ z : α, ∃ a ∈ s, d a z < r)
    (hOsc : ∀ a z : α, d a z < r →
      |(f z - theta * g z) - (f a - theta * g a)| < eta) :
    {z | theta * g z < f z} ⊆
      ⋃ a ∈ s.filter (fun a => theta * g a < f a + eta),
        {z | d a z < r} := by
  classical
  intro z hz
  obtain ⟨a, ha, haz⟩ := hNet z
  have hDelta := (abs_lt.mp (hOsc a z haz)).2
  have hFlag : theta * g a < f a + eta := by
    linarith only [hz, hDelta]
  simp only [Set.mem_iUnion]
  exact ⟨a, Finset.mem_filter.mpr ⟨ha, hFlag⟩, haz⟩

/-- The genuine measure of the exceptional event is at most the finite
sum of the measures of flagged net cells. No disjointness, independence,
or replacement of the original measure is required. -/
theorem p4Q2PZ37AFB_finiteNetExceptionalMass
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν]
    (s : Finset α) (d : α → α → ℝ)
    (r theta eta : ℝ) (f g : α → ℝ)
    (hNet : ∀ z : α, ∃ a ∈ s, d a z < r)
    (hOsc : ∀ a z : α, d a z < r →
      |(f z - theta * g z) - (f a - theta * g a)| < eta) :
    Measure.real ν {z | theta * g z < f z} ≤
      ∑ a ∈ s.filter (fun a => theta * g a < f a + eta),
        Measure.real ν {z | d a z < r} := by
  classical
  calc
    Measure.real ν {z | theta * g z < f z} ≤
        Measure.real ν (⋃ a ∈ s.filter (fun a => theta * g a < f a + eta),
          {z | d a z < r}) :=
      measureReal_mono
        (p4Q2PZ37AFB_finiteNetExceptionalCover
          s d r theta eta f g hNet hOsc)
    _ ≤ _ := measureReal_biUnion_finset_le _ _

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFB_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFB_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFB_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFB_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFB_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFB_probabilityG : IsProbabilityMeasure mu :=
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
local notation "Wz" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Bad" => p4Q2PZ37AFA_originalExceptionalBoundary H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AFB_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFB_pairCompact : CompactSpace Pair := by
  infer_instance
local instance p4Q2PZ37AFB_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Signed physical higher-mode excess at the same true boundary pair,
without changing the receiver, source, measure or Perron weighting. -/
def p4Q2PZ37AFB_originalResidualGap
    (e : Link) (theta : ℝ) (z : Pair) : ℝ :=
  Wz b0 hb0 e z - theta * (A b0 hb0 e z)^2
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H

/-- The original residual gap is continuous on the genuine compact
pair of SU(2) boundary spaces, including its true Perron factor. -/
theorem p4Q2PZ37AFB_originalResidualGap_continuous
    (e : Link) (theta : ℝ) :
    Continuous (Gap e theta) := by
  exact
    (p4Q2PZ37ACR_originalResidual_continuous H b0 hb0 e).sub
      (continuous_const.mul
        (p4Q2PZ37ACN_originalAmplitude_sq_continuous H b0 hb0 e))

/-- Compactness provides an unconditional finite-H uniform modulus of
the *original* gap in the same calibrated full boundary distance D_H. -/
theorem p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
    (e : Link) (theta eta : ℝ) (hEta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∀ a z : Pair,
      D a z < r → |Gap e theta z - Gap e theta a| < eta := by
  exact p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
    D (p4Q2PZ37ADM_originalFullDistance_jointContinuous H)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_eq_zero_iff H z w)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_nonneg H z w)
    (Gap e theta)
    (p4Q2PZ37AFB_originalResidualGap_continuous H e theta)
    eta hEta

/-- The finite table of actual, guard-failing original boundary centers. -/
def p4Q2PZ37AFB_originalFlaggedNetCenters
    (e : Link) (s : Finset Pair) (theta eta : ℝ) : Finset Pair :=
  s.filter (fun a =>
    theta * (A b0 hb0 e a)^2 < Wz b0 hb0 e a + eta)
local notation "Flag" => p4Q2PZ37AFB_originalFlaggedNetCenters H

/-- All true AFA exceptional boundaries lie in flagged original D_H
net balls, provided the actual global oscillation certificate is given. -/
theorem p4Q2PZ37AFB_originalExceptionalBoundary_netCover
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta) :
    Bad e theta ⊆ ⋃ a ∈ Flag e s theta eta, Ball a r := by
  classical
  exact p4Q2PZ37AFB_finiteNetExceptionalCover
    s D r theta eta
    (Wz b0 hb0 e) (fun z : Pair => (A b0 hb0 e z)^2)
    hNet hOsc

/-- A certified *actual* finite boundary net gives an upper bound on
the *true* exceptional pair-Haar mass, in terms of finitely many
measurable original D_H-ball masses. -/
theorem p4Q2PZ37AFB_originalExceptionalBoundary_netMass
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta) :
    Measure.real outer (Bad e theta) ≤
      ∑ a ∈ Flag e s theta eta, Measure.real outer (Ball a r) := by
  classical
  exact p4Q2PZ37AFB_finiteNetExceptionalMass
    outer s D r theta eta
    (Wz b0 hb0 e) (fun z : Pair => (A b0 hb0 e z)^2)
    hNet hOsc

/-- For each finite H, each actual physical link and every positive
guard margin, finite original-D_H net certificates exist. This is an
existence result: it does NOT assert that the finite sum is small. -/
theorem p4Q2PZ37AFB_originalExceptionalFiniteCertificate_exists
    (e : Link) (theta eta : ℝ) (hEta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∃ s : Finset Pair,
      p4Q2PZ37AEE_isOriginalFullNet H s r ∧
      Measure.real outer (Bad e theta) ≤
        ∑ a ∈ Flag e s theta eta, Measure.real outer (Ball a r) := by
  obtain ⟨r, hr, hOsc⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e theta eta hEta
  obtain ⟨s, hNet⟩ :=
    p4Q2PZ37AEE_originalFullFiniteNet_exists H r hr
  exact ⟨r, hr, s, hNet,
    p4Q2PZ37AFB_originalExceptionalBoundary_netMass
      H e theta eta r s hNet hOsc⟩

/-- An independently certified Haar upper bound on each flagged
original D_H ball yields a finite-count exceptional-mass certificate. -/
theorem p4Q2PZ37AFB_originalFlaggedBallCap_mass
    (e : Link) (theta eta r cap : ℝ) (s : Finset Pair)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hBall : ∀ a ∈ Flag e s theta eta,
      Measure.real outer (Ball a r) ≤ cap) :
    Measure.real outer (Bad e theta) ≤
      (Flag e s theta eta).card * cap := by
  classical
  have hMass :=
    p4Q2PZ37AFB_originalExceptionalBoundary_netMass
      H e theta eta r s hNet hOsc
  have hSum :
      (∑ a ∈ Flag e s theta eta, Measure.real outer (Ball a r)) ≤
        ∑ _a ∈ Flag e s theta eta, cap := by
    apply Finset.sum_le_sum
    intro a ha
    exact hBall a ha
  calc
    Measure.real outer (Bad e theta) ≤
        ∑ a ∈ Flag e s theta eta, Measure.real outer (Ball a r) := hMass
    _ ≤ ∑ _a ∈ Flag e s theta eta, cap := hSum
    _ = (Flag e s theta eta).card * cap := by
      simp [nsmul_eq_mul]

/-- This is the AFA positive genuine mean-GI threshold using a
finite table of flagged original net balls rather than an assumed
whole-boundary residual-to-signal inequality. -/
theorem p4Q2PZ37AFB_originalCertifiedNet_gives_positiveBudget
    (e : Link) (theta eta r epsilon : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSum : (∑ a ∈ Flag e s theta eta,
      Measure.real outer (Ball a r)) ≤ epsilon)
    (hNumerical :
      theta * A4 e + (B b0 hb0)^2 * epsilon < 64 * A4 e) :
    0 < Budget b0 hb0 e := by
  have hMass : Measure.real outer (Bad e theta) ≤ epsilon :=
    (p4Q2PZ37AFB_originalExceptionalBoundary_netMass
      H e theta eta r s hNet hOsc).trans hSum
  exact p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    H e theta epsilon hTheta hMass hNumerical

/-- The very same finite genuine-Haar certificate propagates to the
original signed two-posterior response on a positive-measure open set. -/
theorem p4Q2PZ37AFB_originalCertifiedNet_gives_openGI
    (e : Link) (theta eta r epsilon : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSum : (∑ a ∈ Flag e s theta eta,
      Measure.real outer (Ball a r)) ≤ epsilon)
    (hNumerical :
      theta * A4 e + (B b0 hb0)^2 * epsilon < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  have hp := p4Q2PZ37AFB_originalCertifiedNet_gives_positiveBudget
    H e theta eta r epsilon s hTheta hNet hOsc hSum hNumerical
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e hp

/-- The independently certified original FC slack remains necessary
for the stronger original full-moment FC criterion. -/
theorem p4Q2PZ37AFB_originalCertifiedNetFC_gives_trueFC
    (e : Link) (theta eta r sigma epsilon : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSum : (∑ a ∈ Flag e s theta eta,
      Measure.real outer (Ball a r)) ≤ epsilon)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumerical :
      (theta + sigma) * A4 e + (B b0 hb0)^2 * epsilon <
        64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  have hMass : Measure.real outer (Bad e theta) ≤ epsilon :=
    (p4Q2PZ37AFB_originalExceptionalBoundary_netMass
      H e theta eta r s hNet hOsc).trans hSum
  exact p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    H e theta sigma epsilon hTheta hMass hSlack hNumerical

/-- A failed physical mean-GI certificate forces an explicit lower
floor on every certified finite cover's flagged-ball mass sum.
This is not AEX's two-ball no-go and not GI vanishing. -/
theorem p4Q2PZ37AFB_nonpositiveBudget_flaggedSum_floor
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - theta) * A4 e) / (B b0 hb0)^2 ≤
      ∑ a ∈ Flag e s theta eta,
        Measure.real outer (Ball a r) := by
  exact (p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    H e theta hTheta hNonpos).trans
      (p4Q2PZ37AFB_originalExceptionalBoundary_netMass
        H e theta eta r s hNet hOsc)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFB_finiteNetExceptionalCover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFB_finiteNetExceptionalMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalResidualGap_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalExceptionalBoundary_netCover
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalExceptionalBoundary_netMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalExceptionalFiniteCertificate_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalFlaggedBallCap_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalCertifiedNet_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalCertifiedNet_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_originalCertifiedNetFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFB_nonpositiveBudget_flaggedSum_floor
