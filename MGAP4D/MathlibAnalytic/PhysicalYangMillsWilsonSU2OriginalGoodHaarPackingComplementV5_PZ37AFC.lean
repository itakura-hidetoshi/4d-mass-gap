import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExceptionalHaarFiniteNetCertificateV5_PZ37AFB
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPairHaarExplicitFloorV5_PZ37AEA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFC — genuine good-region Haar packing and complementary exceptional mass

Continue the verified AFB finite-net tail certificate and AFA's TRUE original
Wilson/Perron-weighted exceptional residual. This is a complementary route:
rather than supplying upper masses for flagged exceptional balls, certify
good original boundary centers with a strict oscillation margin; select
mutually separated actual D_H balls. ADL's triangle inequality gives true
disjointness. AEA supplies the unconditional, explicit H-dependent lower
Haar mass of EACH genuine good ball.

For t certified good centers, separation D_H(a,b)>=2*r and the true
residual-gap modulus give:

  nu_H(Bad_theta) <= 1 - sum_{a in t} nu_H(B_D(a,r))
                  <= 1 - card(t) * kappa(r/(2*card(Link_H)+1))^(2*card(Link_H)).

This is the SAME original outer pair-Haar probability, with no independent
sampling, changed source/transfer, or substitute geometry. Combining with
AFA's integral gate yields conditional genuine squared GI and FC endpoints.
No existence of a numerically large separated good packing, uniform-H
packing density, or physical mass gap is asserted. The AEX conservative
two-ball FC no-go remains valid.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A certified good-center negative gap and verified local oscillation
exclude any strict-positive residual gap throughout its entire cell. -/
theorem p4Q2PZ37AFC_goodMargin_excludesPositive
    (x y eta : ℝ) (hx : x + eta ≤ 0)
    (hOsc : |y - x| < eta) : ¬ 0 < y := by
  intro hy
  have hdelta := (abs_lt.mp hOsc).2
  linarith only [hx, hdelta, hy]

/-- General genuine probability-space complementary budget for a finite
disjoint family of measurable good cells. -/
theorem p4Q2PZ37AFC_probabilityDisjointGoodCells_tailUpper
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] (bad : Set α)
    (s : Finset α) (cells : α → Set α)
    (hAvoid : bad ⊆ (⋃ a ∈ s, cells a)ᶜ)
    (hUnionMeas : MeasurableSet (⋃ a ∈ s, cells a))
    (hCellsMeas : ∀ a ∈ s, MeasurableSet (cells a))
    (hDisjoint : Set.PairwiseDisjoint (↑s) cells) :
    Measure.real ν bad ≤
      1 - ∑ a ∈ s, Measure.real ν (cells a) := by
  have hMono : Measure.real ν bad ≤
      Measure.real ν (⋃ a ∈ s, cells a)ᶜ :=
    measureReal_mono hAvoid (measure_lt_top ν _).ne
  rw [probReal_compl_eq_one_sub hUnionMeas,
    measureReal_biUnion_finset hDisjoint hCellsMeas] at hMono
  exact hMono

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFC_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFC_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFC_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFC_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFC_probabilityG : IsProbabilityMeasure mu :=
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
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H
local notation "Bad" => p4Q2PZ37AFA_originalExceptionalBoundary H
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "κ" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AFC_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFC_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- A good sample has an actual residual margin greater than its
verified original gap oscillation error. -/
def p4Q2PZ37AFC_originalGoodCenters
    (e : Link) (s : Finset Pair) (theta eta : ℝ) : Finset Pair :=
  s.filter (fun a =>
    Wz b0 hb0 e a + eta ≤ theta * (A b0 hb0 e a)^2)
local notation "Good" => p4Q2PZ37AFC_originalGoodCenters H

/-- The original calibrated full-link D_H triangle inequality converts
a verifiable 2r center separation into genuinely disjoint open balls. -/
theorem p4Q2PZ37AFC_originalSeparatedBalls_disjoint
    (a b : Pair) (r : ℝ) (hSep : 2 * r ≤ D a b) :
    Disjoint (Ball a r) (Ball b r) := by
  apply Set.disjoint_left.mpr
  intro z hza hzb
  change D a z < r at hza
  change D b z < r at hzb
  have hTri := p4Q2PZ37ADL_originalFullDistance_triangle H a z b
  rw [p4Q2PZ37ADL_originalFullDistance_symm H z b] at hTri
  linarith only [hSep, hTri, hza, hzb]

/-- No actual AFA bad boundary is allowed inside an actual good
center's D_H ball under the SAME residual-gap oscillation modulus. -/
theorem p4Q2PZ37AFC_originalGoodCenterBall_avoidsBad
    (e : Link) (theta eta r : ℝ) (a : Pair)
    (hGood : Wz b0 hb0 e a + eta ≤ theta * (A b0 hb0 e a)^2)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta) :
    Ball a r ⊆ (Bad e theta)ᶜ := by
  intro z hz hzBad
  have hdelta := (abs_lt.mp (hOsc a z hz)).2
  change theta * (A b0 hb0 e z)^2 < Wz b0 hb0 e z at hzBad
  dsimp [p4Q2PZ37AFB_originalResidualGap] at hdelta
  linarith only [hGood, hdelta, hzBad]

/-- Every selected genuine good ball is outside AFA's bad set, hence
AFA's exception lies inside the complement of the good-ball union. -/
theorem p4Q2PZ37AFC_originalGoodBalls_complementCoversBad
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta) :
    Bad e theta ⊆
      (⋃ a ∈ Good e s theta eta, Ball a r)ᶜ := by
  classical
  intro z hz hzUnion
  simp only [Set.mem_iUnion] at hzUnion
  obtain ⟨a, ha, hza⟩ := hzUnion
  have hGood : Wz b0 hb0 e a + eta ≤ theta * (A b0 hb0 e a)^2 :=
    (Finset.mem_filter.mp ha).2
  have hAvoid :=
    p4Q2PZ37AFC_originalGoodCenterBall_avoidsBad
      H e theta eta r a hGood hOsc hza
  exact hAvoid hz

/-- Separation of every two distinct certified good centers gives
pairwise disjointness of their TRUE full-boundary D_H balls. -/
theorem p4Q2PZ37AFC_originalGoodBalls_pairwiseDisjoint
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b) :
    Set.PairwiseDisjoint (↑(Good e s theta eta))
      (fun a : Pair => Ball a r) := by
  intro a ha b hb hab
  exact p4Q2PZ37AFC_originalSeparatedBalls_disjoint
    H a b r (hSep a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) hab)

/-- A certified TRUE separated good packing controls original
exceptional pair-Haar mass by the COMPLEMENT of the exact good balls.
No assumed ball measure ceiling or independence enters. -/
theorem p4Q2PZ37AFC_originalSeparatedGoodBalls_tailUpper
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b) :
    Measure.real outer (Bad e theta) ≤
      1 - ∑ a ∈ Good e s theta eta, Measure.real outer (Ball a r) := by
  classical
  have hOpen : IsOpen (⋃ a ∈ Good e s theta eta, Ball a r) := by
    apply isOpen_iUnion
    intro a
    apply isOpen_iUnion
    intro ha
    exact p4Q2PZ37ADL_originalFullChordalBall_isOpen H a r
  have hMeas : ∀ a ∈ Good e s theta eta, MeasurableSet (Ball a r) := by
    intro a ha
    exact (p4Q2PZ37ADL_originalFullChordalBall_isOpen H a r).measurableSet
  exact p4Q2PZ37AFC_probabilityDisjointGoodCells_tailUpper
    outer (Bad e theta) (Good e s theta eta) (fun a : Pair => Ball a r)
    (p4Q2PZ37AFC_originalGoodBalls_complementCoversBad
      H e theta eta r s hOsc)
    hOpen.measurableSet hMeas
    (p4Q2PZ37AFC_originalGoodBalls_pairwiseDisjoint
      H e theta eta r s hSep)

/-- AEA's explicit genuine Haar lower bound is installed in EVERY
certified disjoint good ball simultaneously. No H-independent floor. -/
theorem p4Q2PZ37AFC_originalSeparatedGoodBalls_explicitHaarFloor_upper
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hr : 0 < r)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b) :
    Measure.real outer (Bad e theta) ≤
      1 - (Good e s theta eta).card *
        κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) := by
  let floor : ℝ :=
    κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
      (2 * Fintype.card Link)
  have hSumFloor :
      (∑ a ∈ Good e s theta eta, floor) ≤
        ∑ a ∈ Good e s theta eta, Measure.real outer (Ball a r) := by
    apply Finset.sum_le_sum
    intro a ha
    exact p4Q2PZ37AEA_originalFullBall_mass_ge_explicit H a r hr
  have hExact :=
    p4Q2PZ37AFC_originalSeparatedGoodBalls_tailUpper
      H e theta eta r s hOsc hSep
  have hConstant :
      (∑ _a ∈ Good e s theta eta, floor) =
        (Good e s theta eta).card * floor := by
    simp [nsmul_eq_mul]
  change Measure.real outer (Bad e theta) ≤
    1 - (Good e s theta eta).card * floor
  rw [hConstant] at hSumFloor
  linarith only [hExact, hSumFloor]

/-- A physically certified separated good packing, if its EXPLICIT
AEA mass budget beats AFA's 64 gate, proves the original mean GI
certificate for the SAME centered Gauss-law Wilson source. -/
theorem p4Q2PZ37AFC_originalGoodPacking_gives_positiveBudget
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b)
    (hNumerical :
      theta * A4 e +
        (B b0 hb0)^2 *
          (1 - (Good e s theta eta).card *
            κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
              (2 * Fintype.card Link)) < 64 * A4 e) :
    0 < Budget b0 hb0 e := by
  have hMass :=
    p4Q2PZ37AFC_originalSeparatedGoodBalls_explicitHaarFloor_upper
      H e theta eta r s hr hOsc hSep
  exact p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    H e theta
    (1 - (Good e s theta eta).card *
      κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link))
    hTheta hMass hNumerical

/-- The actual separated good Haar packing propagates to a nonzero
signed genuine Wilson two-posterior GI response on an open Haar region. -/
theorem p4Q2PZ37AFC_originalGoodPacking_gives_openGI
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b)
    (hNumerical :
      theta * A4 e +
        (B b0 hb0)^2 *
          (1 - (Good e s theta eta).card *
            κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
              (2 * Fintype.card Link)) < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e
    (p4Q2PZ37AFC_originalGoodPacking_gives_positiveBudget
      H e theta eta r s hTheta hr hOsc hSep hNumerical)

/-- The stronger TRUE full-moment FC test additionally requires a
separate genuine unused-envelope control E<=sigma*A4, exactly as AFA. -/
theorem p4Q2PZ37AFC_originalGoodPackingFC_gives_trueFC
    (e : Link) (theta eta r sigma : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumerical :
      (theta + sigma) * A4 e +
        (B b0 hb0)^2 *
          (1 - (Good e s theta eta).card *
            κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
              (2 * Fintype.card Link)) < 64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  have hMass :=
    p4Q2PZ37AFC_originalSeparatedGoodBalls_explicitHaarFloor_upper
      H e theta eta r s hr hOsc hSep
  exact p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    H e theta sigma
    (1 - (Good e s theta eta).card *
      κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link))
    hTheta hMass hSlack hNumerical

/-- If the original mean squared GI certificate is nonpositive, NO
genuine separated-good-packing certificate can exceed the complementary
probability left by AFA's necessary exceptional Haar-mass floor. -/
theorem p4Q2PZ37AFC_nonpositiveBudget_limits_goodPacking
    (e : Link) (theta eta r : ℝ) (s : Finset Pair)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hOsc : ∀ x y : Pair, D x y < r →
      |Gap e theta y - Gap e theta x| < eta)
    (hSep : ∀ a ∈ Good e s theta eta,
      ∀ b ∈ Good e s theta eta, a ≠ b → 2 * r ≤ D a b)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - theta) * A4 e) / (B b0 hb0)^2 +
      (Good e s theta eta).card *
        κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
          (2 * Fintype.card Link) ≤ 1 := by
  have hLower :=
    p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
      H e theta hTheta hNonpos
  have hUpper :=
    p4Q2PZ37AFC_originalSeparatedGoodBalls_explicitHaarFloor_upper
      H e theta eta r s hr hOsc hSep
  linarith only [hLower, hUpper]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFC_goodMargin_excludesPositive
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFC_probabilityDisjointGoodCells_tailUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalSeparatedBalls_disjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalGoodCenterBall_avoidsBad
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalGoodBalls_complementCoversBad
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalGoodBalls_pairwiseDisjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalSeparatedGoodBalls_tailUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalSeparatedGoodBalls_explicitHaarFloor_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalGoodPacking_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalGoodPacking_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_originalGoodPackingFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFC_nonpositiveBudget_limits_goodPacking
