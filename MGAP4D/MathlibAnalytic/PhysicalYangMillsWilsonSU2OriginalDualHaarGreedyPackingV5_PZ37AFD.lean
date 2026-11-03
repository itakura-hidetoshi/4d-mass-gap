import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalGoodHaarPackingComplementV5_PZ37AFC
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFD — dual original exceptional Haar certificates and finite good packing extraction

AFB controls the genuine exceptional Haar set by the total measure of
flagged actual D_H balls. AFC controls it by subtracting the measure of
certified separated good balls. This module combines both estimates into
their MINIMUM, without changing the genuine Wilson SU(2) source, Perron
factor, updated transfer, original boundary-pair Haar law, or FC envelope.

New finite combinatorics: from ANY finite set of actual good boundary
centers and any positive r, select a subset of 2r-separated centers
such that EVERY original good center lies <2r from a selected center.
The selection's construction is by finite induction and does not
assume the input good centers are separated. This maximality is
finite-sample coverage, NOT a claim that good centers are numerous.

For an original certified net s, good packing t, and true residual-gap
modulus at radius r, the quantitative exact-source certificate is

  nu_H(Bad_theta)
    <= min( sum_{a in Flag(s)} nu_H(B_D(a,r)),
             1 - card(t) * kappa(r/(2*card(Link_H)+1))^(2*card(Link_H)) ).

This dual upper bound connects to the original AFA 64*weighted-signal
mean-GI gate and, with independent unused FC slack, the stronger FC gate.
The lower obstruction for failed original mean-GI also transfers.

All H-uniform estimates, numerical certified good center counts,
explicit numerical ball upper measures, strict GI threshold, physical
Hamiltonian mass gap and continuum Yang--Mills mass gap remain unproved.
AEX's conservative two-ball FC no-go is unaffected.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Finite greedy 2r-packing with finite sample coverage:
from any finite set, select pairwise separated centers while every
original center remains within strict 2r of a selected center.
The separating function needs only reflexivity and symmetry, not
a false global packing cardinality estimate. -/
theorem p4Q2PZ37AFD_finiteGreedySeparatedSubcover
    {α : Type*} (s : Finset α) (d : α → α → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hSelf : ∀ a : α, d a a = 0)
    (hSymm : ∀ a b : α, d a b = d b a) :
    ∃ t : Finset α, t ⊆ s ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ d a b) ∧
      (∀ a ∈ s, ∃ b ∈ t, d a b < 2 * r) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨∅, by simp, ?_, ?_⟩
      · intro a ha
        simp at ha
      · intro a ha
        simp at ha
  | @insert a s ha ih =>
      obtain ⟨t, htSub, htSep, htCover⟩ := ih
      by_cases hNear : ∃ b ∈ t, d a b < 2 * r
      · refine ⟨t, ?_, htSep, ?_⟩
        · intro x hx
          exact Finset.mem_insert_of_mem (htSub hx)
        · intro x hx
          rcases Finset.mem_insert.mp hx with hxa | hxs
          · subst x
            exact hNear
          · exact htCover x hxs
      · refine ⟨insert a t, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_insert.mp hx with hxa | hxt
          · subst x
            exact Finset.mem_insert_self a s
          · exact Finset.mem_insert_of_mem (htSub hxt)
        · intro x hx y hy hxy
          rcases Finset.mem_insert.mp hx with hxa | hxt
          · subst x
            rcases Finset.mem_insert.mp hy with hya | hyt
            · subst y
              exact False.elim (hxy rfl)
            · exact le_of_not_gt (fun h : d a y < 2 * r =>
                hNear ⟨y, hyt, h⟩)
          · rcases Finset.mem_insert.mp hy with hya | hyt
            · subst y
              have hFar : ¬ d a x < 2 * r :=
                fun h => hNear ⟨x, hxt, h⟩
              rw [hSymm x a]
              exact le_of_not_gt hFar
            · exact htSep x hxt y hyt hxy
        · intro x hx
          rcases Finset.mem_insert.mp hx with hxa | hxs
          · subst x
            refine ⟨a, Finset.mem_insert_self a t, ?_⟩
            rw [hSelf]
            linarith only [hr]
          · obtain ⟨b, hb, hClose⟩ := htCover x hxs
            exact ⟨b, Finset.mem_insert_of_mem hb, hClose⟩

/-- Two established upper bounds combine into their genuine minimum;
the minimum is no invented new probability measure. -/
theorem p4Q2PZ37AFD_realDualUpper
    (mass flagged complementary : ℝ)
    (hFlag : mass ≤ flagged)
    (hComplement : mass ≤ complementary) :
    mass ≤ min flagged complementary :=
  le_min hFlag hComplement

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFD_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFD_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFD_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFD_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFD_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFD_probabilityG : IsProbabilityMeasure mu :=
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
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H
local notation "Bad" => p4Q2PZ37AFA_originalExceptionalBoundary H
local notation "Flag" => p4Q2PZ37AFB_originalFlaggedNetCenters H
local notation "Good" => p4Q2PZ37AFC_originalGoodCenters H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "κ" => p4Q2PZ37ADQ_sphereRadiusFraction

local instance p4Q2PZ37AFD_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFD_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Exact true finite-volume AEA radius floor; no numeric or H-uniform
lower bound beyond AEA is inserted. -/
def p4Q2PZ37AFD_originalHaarBallFloor (r : ℝ) : ℝ :=
  κ (r / (2 * (Fintype.card Link : ℝ) + 1)) ^
    (2 * Fintype.card Link)
local notation "floor" => p4Q2PZ37AFD_originalHaarBallFloor H

/-- Original physical dual cert: FLAGGED genuine Haar ball upper sum
against the complementary lower mass of a selected good packing. -/
def p4Q2PZ37AFD_originalDualExceptionalHaarBudget
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ) : ℝ :=
  min
    (∑ a ∈ Flag e s theta eta, Measure.real outer (Ball a r))
    (1 - (t.card : ℝ) * floor r)
local notation "Dual" => p4Q2PZ37AFD_originalDualExceptionalHaarBudget H

/-- On the genuine same finite boundary net s, the AFB good filter
is inherited by any selected subset t of the AFB/AFC good centers. -/
theorem p4Q2PZ37AFD_selectedOriginalGoodFilter_eq
    (e : Link) (s t : Finset Pair) (theta eta : ℝ)
    (hSub : t ⊆ Good e s theta eta) :
    Good e t theta eta = t := by
  classical
  ext a
  constructor
  · intro ha
    exact (Finset.mem_filter.mp ha).1
  · intro ha
    have hGood := (Finset.mem_filter.mp (hSub ha)).2
    exact Finset.mem_filter.mpr ⟨ha, hGood⟩

/-- A true original-good subset's 2r separation transports unchanged
to AFC's exact good filter on the selected sample list. -/
theorem p4Q2PZ37AFD_selectedOriginalGoodPacking_separated
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b) :
    ∀ a ∈ Good e t theta eta,
      ∀ b ∈ Good e t theta eta, a ≠ b → 2 * r ≤ D a b := by
  rw [p4Q2PZ37AFD_selectedOriginalGoodFilter_eq H e s t theta eta hSub]
  exact hSep

/-- Every actual finite set of genuine GOOD centers contains a
2r-separated subpacking that covers all the original good samples
at radius 2r. This removes AFC's externally supplied separation
premise for an *extracted* finite sample. -/
theorem p4Q2PZ37AFD_originalGreedyGoodPacking_exists
    (e : Link) (s : Finset Pair) (theta eta r : ℝ) (hr : 0 < r) :
    ∃ t : Finset Pair, t ⊆ Good e s theta eta ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b) ∧
      (∀ a ∈ Good e s theta eta,
        ∃ b ∈ t, D a b < 2 * r) := by
  exact p4Q2PZ37AFD_finiteGreedySeparatedSubcover
    (Good e s theta eta) D r hr
    (p4Q2PZ37ADL_originalFullDistance_self H)
    (p4Q2PZ37ADL_originalFullDistance_symm H)

/-- The genuine AFB and AFC source-fixed Haar upper estimates combine
on one actual finite net s with a selected 2r-separated GOOD subset t.
The positive AEA ball floor is unchanged. -/
theorem p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ)
    (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b) :
    Measure.real outer (Bad e theta) ≤ Dual e s t theta eta r := by
  have hFlag :=
    p4Q2PZ37AFB_originalExceptionalBoundary_netMass
      H e theta eta r s hNet hOsc
  have hSepAFC :=
    p4Q2PZ37AFD_selectedOriginalGoodPacking_separated
      H e s t theta eta r hSub hSep
  have hGood :=
    p4Q2PZ37AFC_originalSeparatedGoodBalls_explicitHaarFloor_upper
      H e theta eta r t hr hOsc hSepAFC
  have hGoodEq :=
    p4Q2PZ37AFD_selectedOriginalGoodFilter_eq
      H e s t theta eta hSub
  rw [hGoodEq] at hGood
  change Measure.real outer (Bad e theta) ≤
    min (∑ a ∈ Flag e s theta eta, Measure.real outer (Ball a r))
      (1 - (t.card : ℝ) * floor r)
  exact p4Q2PZ37AFD_realDualUpper _ _ _ hFlag hGood

/-- The same ORIGINAL dual Haar budget cannot be negative when its
actual source, coverage, oscillation and good packing are certified. -/
theorem p4Q2PZ37AFD_originalDualBudget_nonneg
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ)
    (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b) :
    0 ≤ Dual e s t theta eta r := by
  have hMass := p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
    H e s t theta eta r hr hNet hOsc hSub hSep
  exact (measureReal_nonneg).trans hMass

/-- No separated subset is an external existential assumption:
finite greedy selection constructs a dual AFB/AFC Haar certificate
from any certified original physical net and gap modulus. -/
theorem p4Q2PZ37AFD_originalExtractedDualCertificate_exists
    (e : Link) (s : Finset Pair) (theta eta r : ℝ)
    (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta) :
    ∃ t : Finset Pair, t ⊆ Good e s theta eta ∧
      (∀ a ∈ Good e s theta eta, ∃ b ∈ t, D a b < 2 * r) ∧
      Measure.real outer (Bad e theta) ≤ Dual e s t theta eta r := by
  obtain ⟨t, hSub, hSep, hCover⟩ :=
    p4Q2PZ37AFD_originalGreedyGoodPacking_exists
      H e s theta eta r hr
  exact ⟨t, hSub, hCover,
    p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
      H e s t theta eta r hr hNet hOsc hSub hSep⟩

/-- Genuine fixed-H dual certificates exist for every strictly
positive guard margin; the chosen net, radius and packing are
mathematical witnesses, NOT evaluated numerical inputs. -/
theorem p4Q2PZ37AFD_originalEveryMargin_dualCertificate_exists
    (e : Link) (theta eta : ℝ) (hEta : 0 < eta) :
    ∃ r : ℝ, 0 < r ∧ ∃ s t : Finset Pair,
      p4Q2PZ37AEE_isOriginalFullNet H s r ∧
      t ⊆ Good e s theta eta ∧
      (∀ a ∈ Good e s theta eta, ∃ b ∈ t, D a b < 2 * r) ∧
      Measure.real outer (Bad e theta) ≤ Dual e s t theta eta r := by
  obtain ⟨r, hr, hOsc⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e theta eta hEta
  obtain ⟨s, hNet⟩ :=
    p4Q2PZ37AEE_originalFullFiniteNet_exists H r hr
  obtain ⟨t, hSub, hCover, hBound⟩ :=
    p4Q2PZ37AFD_originalExtractedDualCertificate_exists
      H e s theta eta r hr hNet hOsc
  exact ⟨r, hr, s, t, hNet, hSub, hCover, hBound⟩

/-- A separately numerically certified ORIGINAL dual Haar budget
meeting the unchanged AFA 64 threshold gives positive squared mean GI. -/
theorem p4Q2PZ37AFD_originalDualBudget_gives_positiveGI
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b)
    (hNumerical : theta * A4 e +
      (B b0 hb0)^2 * Dual e s t theta eta r < 64 * A4 e) :
    0 < Budget b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    H e theta (Dual e s t theta eta r)
    hTheta
    (p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
      H e s t theta eta r hr hNet hOsc hSub hSep)
    hNumerical

/-- The exact original Wilson two-posterior signed gap inherits
a nonzero open genuine pair-Haar region from the dual certificate. -/
theorem p4Q2PZ37AFD_originalDualBudget_gives_openGI
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b)
    (hNumerical : theta * A4 e +
      (B b0 hb0)^2 * Dual e s t theta eta r < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e
    (p4Q2PZ37AFD_originalDualBudget_gives_positiveGI
      H e s t theta eta r hTheta hr hNet hOsc hSub hSep hNumerical)

/-- Strict original FC comparison from the same dual genuine-Haar
certificate still requires independent original unused-envelope slack. -/
theorem p4Q2PZ37AFD_originalDualBudgetFC_gives_trueFC
    (e : Link) (s t : Finset Pair) (theta eta r sigma : ℝ)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumerical : (theta + sigma) * A4 e +
      (B b0 hb0)^2 * Dual e s t theta eta r < 64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    H e theta sigma (Dual e s t theta eta r)
    hTheta
    (p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
      H e s t theta eta r hr hNet hOsc hSub hSep)
    hSlack hNumerical

/-- The stronger original FC certificate also propagates through the
unchanged signed two-posterior physical GI theorem. -/
theorem p4Q2PZ37AFD_originalDualBudgetFC_gives_openGI
    (e : Link) (s t : Finset Pair) (theta eta r sigma : ℝ)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumerical : (theta + sigma) * A4 e +
      (B b0 hb0)^2 * Dual e s t theta eta r < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_openGI H e
    (p4Q2PZ37AFD_originalDualBudgetFC_gives_trueFC
      H e s t theta eta r sigma hTheta hr hNet hOsc hSub hSep
      hSlack hNumerical)

/-- If the original mean squared GI certificate fails, the new
MINIMUM of both verified true Haar upper budgets cannot fall below
AFA's genuine necessary exceptional mass. -/
theorem p4Q2PZ37AFD_nonpositiveBudget_dualHaar_floor
    (e : Link) (s t : Finset Pair) (theta eta r : ℝ)
    (hTheta : 0 ≤ theta) (hr : 0 < r)
    (hNet : p4Q2PZ37AEE_isOriginalFullNet H s r)
    (hOsc : ∀ a z : Pair, D a z < r →
      |Gap e theta z - Gap e theta a| < eta)
    (hSub : t ⊆ Good e s theta eta)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * r ≤ D a b)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - theta) * A4 e) / (B b0 hb0)^2 ≤
      Dual e s t theta eta r := by
  exact (p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    H e theta hTheta hNonpos).trans
    (p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
      H e s t theta eta r hr hNet hOsc hSub hSep)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFD_finiteGreedySeparatedSubcover
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFD_realDualUpper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_selectedOriginalGoodFilter_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_selectedOriginalGoodPacking_separated
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalGreedyGoodPacking_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalDualBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalExtractedDualCertificate_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalEveryMargin_dualCertificate_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalDualBudget_gives_positiveGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalDualBudget_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalDualBudgetFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_originalDualBudgetFC_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFD_nonpositiveBudget_dualHaar_floor
