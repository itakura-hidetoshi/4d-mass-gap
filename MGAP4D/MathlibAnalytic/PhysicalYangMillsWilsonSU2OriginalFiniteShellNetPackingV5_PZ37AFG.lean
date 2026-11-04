import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHierarchicalHaarShellCertificateV5_PZ37AFF
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFG — finite original Wilson/Perron shell-net and packing certificates

AFF constructs a genuine positive-Haar ball in an original exceptional
threshold shell, conditionally on two strict original residual-gap signs.
AFG makes the center selection a FINITE, checkable original boundary-net
filter and extracts an ACTUAL 2r-separated subpacking by AFD's finite
greedy construction. Every selected genuine full-link ball lies in
the SAME true shell; pairwise disjointness is proved using the original
ADL metric rather than a proxy geometry.

For an original net s at radius r, and independently established
original low/high gap oscillation bounds etaLo, etaHi, the finite set
  Robust(s) = {a in s | etaLo < G_lo(a) and G_hi(a) < -etaHi}
supplies certified true shell balls. Any 2r-separated selected subset t
then gives
  card(t)*kappa_H(r) <= nu_H(Shell(lo,hi)).
This is NOT inferred from subtraction of two upper bounds.

If one actual original boundary point has two STRICT opposite gap signs,
a positive-margin finite net with a robust center exists by AFB/AEE.
This is a conditional detector, NOT unconditional original Wilson gap
crossing or a numerically evaluated certificate.

Combine a genuine packed shell floor with AFE lower/top threshold
tables to produce
  nu_H(Bad_hi) <= min(U_hi, U_lo-card(t)*kappa_H(r)),
and the original AFA mean GI, signed two-posterior GI, independent FC
slack and failed-mean-GI obstruction. AEX's conservative FC no-go,
original Wilson SU(2), ground Perron, Gauss-law source, transfer,
pair-Haar measure, metrics and pinned Lean/mathlib are unchanged.

No actual finite net numerical values, uniformly positive shell-volume
in H, continuum 4D Yang--Mills mass gap or physical spectral gap is
asserted.
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
local instance p4Q2PZ37AFG_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFG_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFG_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFG_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFG_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFG_probabilityG : IsProbabilityMeasure mu :=
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
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H
local notation "Bad" => p4Q2PZ37AFA_originalExceptionalBoundary H
local notation "Shell" => p4Q2PZ37AFF_originalExceptionalShell H
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AFG_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFG_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Data of a REAL finite original full-boundary net with separate
original low and high residual-gap uniform moduli. No numeric Haar
estimate or robust-center count is postulated. -/
structure p4Q2PZ37AFG_originalShellSampleTable
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ) where
  s : Finset
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
  r : ℝ
  etaLo : ℝ
  etaHi : ℝ
  hOrder : lo ≤ hi
  hR : 0 < r
  hEtaLo : 0 < etaLo
  hEtaHi : 0 < etaHi
  hNet : p4Q2PZ37AEE_isOriginalFullNet H s r
  hOscLo : ∀ a z, p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z < r →
    |p4Q2PZ37AFB_originalResidualGap H e lo z -
      p4Q2PZ37AFB_originalResidualGap H e lo a| < etaLo
  hOscHi : ∀ a z, p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z < r →
    |p4Q2PZ37AFB_originalResidualGap H e hi z -
      p4Q2PZ37AFB_originalResidualGap H e hi a| < etaHi

/-- The exact finite filter of actual original physical boundary-pair
samples with two signs robust against the sampled gap oscillation. -/
def p4Q2PZ37AFG_originalRobustShellCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) : Finset Pair :=
  c.s.filter (fun a => c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi)
local notation "Robust" => p4Q2PZ37AFG_originalRobustShellCenters H

/-- A robust sampled center contains precisely the strict two-sided
true Wilson/Perron physical-gap evidence required by AFF. -/
theorem p4Q2PZ37AFG_robustCenter_signs
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (a : Pair) (ha : a ∈ Robust e c) :
    c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi := by
  exact (Finset.mem_filter.mp ha).2

/-- Every candidate of the FINITE table is the center of a true
original full-link ball contained in the true Haar threshold shell. -/
theorem p4Q2PZ37AFG_robustCenter_ball_subset
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (a : Pair) (ha : a ∈ Robust e c) :
    Ball a c.r ⊆ Shell e lo hi := by
  have hSigns := p4Q2PZ37AFG_robustCenter_signs H e c a ha
  let w : p4Q2PZ37AFF_originalShellBall H e lo hi := {
    center := a
    radius := c.r
    marginLo := c.etaLo
    marginHi := c.etaHi
    hRadius := c.hR
    hMarginLo := c.hEtaLo
    hMarginHi := c.hEtaHi
    hOrder := c.hOrder
    hCenterLo := hSigns.1
    hCenterHi := hSigns.2
    hOscLo := fun z hz => c.hOscLo a z hz
    hOscHi := fun z hz => c.hOscHi a z hz
  }
  exact p4Q2PZ37AFF_originalShellBall_subset H e w

/-- Each REAL finite original robust center contributes AEA's
genuine positive, H-dependent pair-Haar floor to the shell. -/
theorem p4Q2PZ37AFG_robustCenter_floor_le_shell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (a : Pair) (ha : a ∈ Robust e c) :
    p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
      Measure.real outer (Shell e lo hi) := by
  exact (p4Q2PZ37AEA_originalFullBall_mass_ge_explicit
    H a c.r c.hR).trans
      (measureReal_mono (p4Q2PZ37AFG_robustCenter_ball_subset
        H e c a ha) (measure_lt_top outer _).ne)

/-- A REAL 2r-separated subpacking of the finite robust sample set
has pairwise disjoint ORIGINAL full-boundary Haar balls. -/
theorem p4Q2PZ37AFG_robustPacking_pairwiseDisjoint
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair) (hSep : ∀ a ∈ t, ∀ b ∈ t,
      a ≠ b → 2 * c.r ≤ D a b) :
    Set.PairwiseDisjoint (↑t) (fun a : Pair => Ball a c.r) := by
  intro a ha b hb hab
  exact p4Q2PZ37AFC_originalSeparatedBalls_disjoint
    H a b c.r (hSep a (Finset.mem_coe.mp ha) b
      (Finset.mem_coe.mp hb) hab)

/-- Multiple genuine robust center balls provide an ADDITIVE original
shell Haar mass floor, not a sum of overlapping full balls. -/
theorem p4Q2PZ37AFG_robustPacking_mass_lower
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t,
      a ≠ b → 2 * c.r ≤ D a b) :
    (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
      Measure.real outer (Shell e lo hi) := by
  classical
  have hUnionSubset :
      (⋃ a ∈ t, Ball a c.r) ⊆ Shell e lo hi := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨a, ha, hza⟩ := hz
    exact p4Q2PZ37AFG_robustCenter_ball_subset H e c a
      (hSelected ha) hza
  have hCells : ∀ a ∈ t, MeasurableSet (Ball a c.r) := by
    intro a _ha
    exact (p4Q2PZ37ADL_originalFullChordalBall_isOpen
      H a c.r).measurableSet
  have hUnion : (∑ a ∈ t, Measure.real outer (Ball a c.r)) ≤
      Measure.real outer (Shell e lo hi) := by
    have hMass : Measure.real outer (⋃ a ∈ t, Ball a c.r) ≤
        Measure.real outer (Shell e lo hi) :=
      measureReal_mono hUnionSubset (measure_lt_top outer _).ne
    rw [measureReal_biUnion_finset
      (p4Q2PZ37AFG_robustPacking_pairwiseDisjoint H e c t hSep)
      hCells] at hMass
    exact hMass
  have hFloors :
      (∑ _a ∈ t, p4Q2PZ37AFD_originalHaarBallFloor H c.r) ≤
        ∑ a ∈ t, Measure.real outer (Ball a c.r) := by
    apply Finset.sum_le_sum
    intro a _ha
    exact p4Q2PZ37AEA_originalFullBall_mass_ge_explicit H a c.r c.hR
  have hCount :
      (∑ _a ∈ t, p4Q2PZ37AFD_originalHaarBallFloor H c.r) =
        (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r := by
    simp [nsmul_eq_mul]
  rw [hCount] at hFloors
  exact hFloors.trans hUnion

/-- Finite AFD greedy selection always EXTRACTS a separated robust
packing from the actual sample table; no false packing-density premise. -/
theorem p4Q2PZ37AFG_robustPacking_exists
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) :
    ∃ t : Finset Pair,
      t ⊆ Robust e c ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b) ∧
      (∀ a ∈ Robust e c, ∃ b ∈ t, D a b < 2 * c.r) ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) := by
  obtain ⟨t, ht, hSep, hCover⟩ :=
    p4Q2PZ37AFD_finiteGreedySeparatedSubcover
      (Robust e c) D c.r c.hR
      (p4Q2PZ37ADL_originalFullDistance_self H)
      (p4Q2PZ37ADL_originalFullDistance_symm H)
  exact ⟨t, ht, hSep, hCover,
    p4Q2PZ37AFG_robustPacking_mass_lower H e c t ht hSep⟩

/-- A finite robust candidate is a verified condition for a
nonempty true packing and a quantitatively positive shell Haar mass. -/
theorem p4Q2PZ37AFG_robustNonempty_positiveShell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hCandidate : (Robust e c).Nonempty) :
    ∃ t : Finset Pair,
      t ⊆ Robust e c ∧
      0 < (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) := by
  obtain ⟨t, ht, _hSep, hCover, hFloor⟩ :=
    p4Q2PZ37AFG_robustPacking_exists H e c
  obtain ⟨a, ha⟩ := hCandidate
  obtain ⟨b, hb, _hNear⟩ := hCover a ha
  have hCardNat : 0 < t.card := Finset.card_pos.mpr ⟨b, hb⟩
  have hCard : (0 : ℝ) < (t.card : ℝ) := by exact_mod_cast hCardNat
  have hRad := p4Q2PZ37AEA_explicitFloor_pos H c.r c.hR
  exact ⟨t, ht, mul_pos hCard hRad, hFloor⟩

/-- For any pair of ordered original thresholds and any separate
positive guard margins, AFB/AEE actually construct a finite original
net with BOTH genuine physical gap moduli at a common radius. -/
theorem p4Q2PZ37AFG_originalSampleTable_exists
    (e : Link) (lo hi etaLo etaHi : ℝ)
    (hOrder : lo ≤ hi) (hEtaLo : 0 < etaLo) (hEtaHi : 0 < etaHi) :
    ∃ c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi,
      c.etaLo = etaLo ∧ c.etaHi = etaHi := by
  obtain ⟨rLo, hrLo, hOscLo⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e lo etaLo hEtaLo
  obtain ⟨rHi, hrHi, hOscHi⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e hi etaHi hEtaHi
  have hr : 0 < min rLo rHi := lt_min hrLo hrHi
  obtain ⟨s, hs⟩ :=
    p4Q2PZ37AEE_originalFullFiniteNet_exists H (min rLo rHi) hr
  refine ⟨{
    s := s
    r := min rLo rHi
    etaLo := etaLo
    etaHi := etaHi
    hOrder := hOrder
    hR := hr
    hEtaLo := hEtaLo
    hEtaHi := hEtaHi
    hNet := hs
    hOscLo := by
      intro a z haz
      exact hOscLo a z (lt_of_lt_of_le haz (min_le_left _ _))
    hOscHi := by
      intro a z haz
      exact hOscHi a z (lt_of_lt_of_le haz (min_le_right _ _))
  }, rfl, rfl⟩

/-- Soundness in the opposite direction: a REAL original point with
a quantitative 2-guard sign margin necessarily appears as a robust
candidate in EVERY sufficiently fine certified finite original net. -/
theorem p4Q2PZ37AFG_originalStrongShellPoint_detected
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (z : Pair)
    (hLow : 2 * c.etaLo < Gap e lo z)
    (hHigh : Gap e hi z < -(2 * c.etaHi)) :
    (Robust e c).Nonempty := by
  obtain ⟨a, ha, haz⟩ := c.hNet z
  have hLOsc := (abs_lt.mp (c.hOscLo a z haz)).2
  have hHOsc := (abs_lt.mp (c.hOscHi a z haz)).1
  refine ⟨a, Finset.mem_filter.mpr ⟨ha, ?_⟩⟩
  constructor
  · linarith only [hLow, hLOsc]
  · linarith only [hHigh, hHOsc]

/-- A true STRICT low-positive/high-negative Wilson/Perron gap
crossing produces a finite ACTUAL original net and a nonempty packed
Haar floor certificate, without supplying any new measure or source. -/
theorem p4Q2PZ37AFG_strictOriginalPoint_gives_finitePacking
    (e : Link) (lo hi : ℝ) (hOrder : lo ≤ hi)
    (z : Pair) (hLo : 0 < Gap e lo z) (hHi : Gap e hi z < 0) :
    ∃ (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
      (t : Finset Pair),
      t ⊆ Robust e c ∧
      0 < (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) := by
  let etaLo : ℝ := Gap e lo z / 4
  let etaHi : ℝ := -(Gap e hi z) / 4
  have hEtaLo : 0 < etaLo := by
    dsimp [etaLo]
    linarith only [hLo]
  have hEtaHi : 0 < etaHi := by
    dsimp [etaHi]
    linarith only [hHi]
  obtain ⟨c, hcLo, hcHi⟩ :=
    p4Q2PZ37AFG_originalSampleTable_exists
      H e lo hi etaLo etaHi hOrder hEtaLo hEtaHi
  have hCandidate : (Robust e c).Nonempty := by
    apply p4Q2PZ37AFG_originalStrongShellPoint_detected H e c z
    · rw [hcLo]
      dsimp [etaLo]
      linarith only [hLo]
    · rw [hcHi]
      dsimp [etaHi]
      linarith only [hHi]
  obtain ⟨t, ht, hPos, hFloor⟩ :=
    p4Q2PZ37AFG_robustNonempty_positiveShell H e c hCandidate
  exact ⟨c, t, ht, hPos, hFloor⟩

/-- The original Wilson/Perron finite packed shell budget uses
independent AFE base/top tables and the AEA cardinal shell floor. -/
def p4Q2PZ37AFG_originalPackedShellBudget
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e)) : ℝ :=
  min (p4Q2PZ37AFE_multiscaleBudget H e topScales)
    (p4Q2PZ37AFE_multiscaleBudget H e baseScales -
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r)

/-- Main AFG packed-shell certificate, with truly disjoint genuine
SU(2) original boundary balls, without double counting any Haar mass. -/
theorem p4Q2PZ37AFG_originalPackedShellHaarMass_upper
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi) :
    Measure.real outer (Bad e hi) ≤
      p4Q2PZ37AFG_originalPackedShellBudget
        H e c t baseScales topScales := by
  have hBaseBound :=
    p4Q2PZ37AFE_multiscaleHaarMass_upper H e lo baseScales hBase
  have hTopBound :=
    p4Q2PZ37AFE_multiscaleHaarMass_upper H e hi topScales hTop
  have hExact := p4Q2PZ37AFF_originalShell_mass_exact
    H e lo hi c.hOrder
  have hPacked := p4Q2PZ37AFG_robustPacking_mass_lower
    H e c t hSelected hSep
  change Measure.real outer (Bad e hi) ≤
    min (p4Q2PZ37AFE_multiscaleBudget H e topScales)
      (p4Q2PZ37AFE_multiscaleBudget H e baseScales -
        (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r)
  apply le_min hTopBound
  linarith only [hBaseBound, hExact, hPacked]

/-- The packed-shell budget is not worse than the original AFE
top-threshold table, regardless of sample count. -/
theorem p4Q2PZ37AFG_originalPackedShellBudget_le_top
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e)) :
    p4Q2PZ37AFG_originalPackedShellBudget
      H e c t baseScales topScales ≤
        p4Q2PZ37AFE_multiscaleBudget H e topScales := by
  exact min_le_left _ _

/-- The same budget cannot exceed the original AFE base threshold
bound: every real AEA original Haar radius floor is positive. -/
theorem p4Q2PZ37AFG_originalPackedShellBudget_le_base
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e)) :
    p4Q2PZ37AFG_originalPackedShellBudget
      H e c t baseScales topScales ≤
        p4Q2PZ37AFE_multiscaleBudget H e baseScales := by
  have hFloor : 0 ≤
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r :=
    mul_nonneg (Nat.cast_nonneg _)
      (le_of_lt (p4Q2PZ37AEA_explicitFloor_pos H c.r c.hR))
  exact (min_le_right _ _).trans (sub_le_self _ hFloor)

/-- Genuine packed-shell upper bounds are [0,1] when their finite
original Wilson/Perron evidence is certified. -/
theorem p4Q2PZ37AFG_originalPackedShellBudget_range
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi) :
    0 ≤ p4Q2PZ37AFG_originalPackedShellBudget
      H e c t baseScales topScales ∧
    p4Q2PZ37AFG_originalPackedShellBudget
      H e c t baseScales topScales ≤ 1 := by
  constructor
  · exact measureReal_nonneg.trans
      (p4Q2PZ37AFG_originalPackedShellHaarMass_upper H e
        c t baseScales topScales hSelected hSep hBase hTop)
  · exact (p4Q2PZ37AFG_originalPackedShellBudget_le_top
      H e c t baseScales topScales).trans
        (p4Q2PZ37AFE_multiscaleBudget_le_one H e topScales)

/-- A separately numerically verified true packed-shell bound
satisfying AFA's unchanged 64 threshold gives positive mean GI. -/
theorem p4Q2PZ37AFG_originalPackedShell_gives_positiveBudget
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hNumeric : hi * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFG_originalPackedShellBudget
          H e c t baseScales topScales < 64 * A4 e) :
    0 < Budget b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    H e hi (p4Q2PZ37AFG_originalPackedShellBudget
      H e c t baseScales topScales)
    hTheta
    (p4Q2PZ37AFG_originalPackedShellHaarMass_upper
      H e c t baseScales topScales hSelected hSep hBase hTop)
    hNumeric

/-- The same original physical two-posterior signed GI response is
nonzero on an open genuine pair-Haar positive-measure set. -/
theorem p4Q2PZ37AFG_originalPackedShell_gives_openGI
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hNumeric : hi * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFG_originalPackedShellBudget
          H e c t baseScales topScales < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion
    H b0 hb0 e
    (p4Q2PZ37AFG_originalPackedShell_gives_positiveBudget
      H e c t baseScales topScales hTheta hSelected hSep
      hBase hTop hNumeric)

/-- The TRUE original FC criterion remains stronger and needs its
separately validated original unused-variance slack sigma. -/
theorem p4Q2PZ37AFG_originalPackedShellFC_gives_trueFC
    (e : Link) {lo hi : ℝ} (sigma : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumeric : (hi + sigma) * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFG_originalPackedShellBudget
          H e c t baseScales topScales < 64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    H e hi sigma (p4Q2PZ37AFG_originalPackedShellBudget
      H e c t baseScales topScales)
    hTheta
    (p4Q2PZ37AFG_originalPackedShellHaarMass_upper
      H e c t baseScales topScales hSelected hSep hBase hTop)
    hSlack hNumeric

/-- A nonpositive genuine original mean squared-GI budget imposes
AFA's true necessary mass floor on EVERY verified packed shell budget.
This is a certificate obstruction, not physical GI vanishing. -/
theorem p4Q2PZ37AFG_nonpositiveBudget_packedShell_floor
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : Finset Pair)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hSelected : t ⊆ Robust e c)
    (hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b)
    (hBase : ∀ w ∈ baseScales, w.theta ≤ lo)
    (hTop : ∀ w ∈ topScales, w.theta ≤ hi)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - hi) * A4 e) / (B b0 hb0)^2 ≤
      p4Q2PZ37AFG_originalPackedShellBudget
        H e c t baseScales topScales := by
  exact (p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    H e hi hTheta hNonpos).trans
      (p4Q2PZ37AFG_originalPackedShellHaarMass_upper
        H e c t baseScales topScales hSelected hSep hBase hTop)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustCenter_signs
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustCenter_ball_subset
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustCenter_floor_le_shell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustPacking_pairwiseDisjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustPacking_mass_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustPacking_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_robustNonempty_positiveShell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalSampleTable_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalStrongShellPoint_detected
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_strictOriginalPoint_gives_finitePacking
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShellHaarMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShellBudget_le_top
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShellBudget_le_base
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShellBudget_range
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShell_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShell_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_originalPackedShellFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFG_nonpositiveBudget_packedShell_floor
