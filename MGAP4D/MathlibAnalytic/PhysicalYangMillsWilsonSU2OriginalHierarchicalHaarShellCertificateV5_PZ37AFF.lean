import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalMultiscaleHaarCertificateV5_PZ37AFE
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFF — genuine nested exceptional Haar shells

AFE bounds the same genuine Wilson/Perron pair-Haar bad event from several
independent scales. AFF retains AFE's finite-table upper bounds and proves
a different, genuinely additive refinement: a certified ORIGINAL shell
between two ordered thresholds can be removed, without double counting,
from the Haar mass of the lower-threshold event.

For θ₀ ≤ θ₁ the true original shell is
  Shell(θ₀, θ₁) = Bad(θ₀) \ Bad(θ₁).
Its real Haar mass is exactly
  ν(Bad(θ₀)) - ν(Bad(θ₁)).

A physical shell-ball certificate retains a genuine boundary pair center,
positive original full-link chordal radius, positive low/high margins and
two ORIGINAL residual-gap oscillation proofs. The low residual gap stays
strictly positive on the ball, while the high residual gap stays strictly
negative. Hence the actual original ball is contained in the true shell
and AEA's unconditional, H-dependent original Haar ball floor applies.

Typed finite chains of adjacent original shell balls telescope without
overlap. Their sum of positive Haar ball floors subtracts from the
original AFE base threshold table, while an independent AFE top table
still applies. The refined upper bound is their true minimum.

A shell ball is only constructed conditionally when a genuine center
has opposite STRICT residual-gap signs. No such center, useful numerical
lower mass, H-uniform estimate, genuine FC slack, Yang--Mills Hamiltonian
gap or continuum 4D mass gap is asserted unconditionally. AEX's
conservative FC two-ball no-go is retained.
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
local instance p4Q2PZ37AFF_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFF_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFF_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFF_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFF_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFF_probabilityG : IsProbabilityMeasure mu :=
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

local instance p4Q2PZ37AFF_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFF_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- The strictly bad original Wilson/Perron boundary is the strictly
POSITIVE original residual-minus-threshold-times-amplitude gap. -/
theorem p4Q2PZ37AFF_originalBad_iff_gap_pos
    (e : Link) (theta : ℝ) (z : Pair) :
    z ∈ Bad e theta ↔ 0 < Gap e theta z := by
  change theta * (A b0 hb0 e z)^2 < Wz b0 hb0 e z ↔
    0 < Wz b0 hb0 e z - theta * (A b0 hb0 e z)^2
  constructor <;> intro h <;> linarith only [h]

/-- Each original shell is a difference of two actual bad-boundary
sets under the SAME genuine original pair-Haar probability. -/
def p4Q2PZ37AFF_originalExceptionalShell
    (e : Link) (lo hi : ℝ) : Set Pair :=
  Bad e lo \ Bad e hi
local notation "Shell" => p4Q2PZ37AFF_originalExceptionalShell H

/-- Original shells are measurable because the underlying true
exceptional events are open. -/
theorem p4Q2PZ37AFF_originalShell_measurable
    (e : Link) (lo hi : ℝ) : MeasurableSet (Shell e lo hi) := by
  exact (p4Q2PZ37AFA_originalExceptionalBoundary_isOpen
    H e lo).measurableSet.diff
      (p4Q2PZ37AFA_originalExceptionalBoundary_isOpen H e hi).measurableSet

/-- Neighboring true shells are disjoint, even without choosing balls
or assigning the same radius to their respective certificates. -/
theorem p4Q2PZ37AFF_originalAdjacentShells_disjoint
    (e : Link) (lo mid hi : ℝ) :
    Disjoint (Shell e lo mid) (Shell e mid hi) := by
  refine Set.disjoint_left.mpr ?_
  intro z hzLeft hzRight
  exact hzLeft.2 hzRight.1

/-- Exact finite original-Haar shell subtraction. The monotonicity
is inherited from the actual nonnegative squared physical amplitude. -/
theorem p4Q2PZ37AFF_originalShell_mass_exact
    (e : Link) (lo hi : ℝ) (hOrder : lo ≤ hi) :
    Measure.real outer (Bad e hi) +
      Measure.real outer (Shell e lo hi) =
        Measure.real outer (Bad e lo) := by
  have hIncl := p4Q2PZ37AFE_originalBad_antitone H e lo hi hOrder
  have hDiff := measureReal_diff hIncl
    (p4Q2PZ37AFA_originalExceptionalBoundary_isOpen H e hi).measurableSet
    (measure_lt_top outer _).ne
  change Measure.real outer (Shell e lo hi) =
    Measure.real outer (Bad e lo) - Measure.real outer (Bad e hi) at hDiff
  linarith only [hDiff]

/-- An original physical shell-ball witness: one actual boundary-pair
ball remains strictly bad at lo and strictly good at hi, certified by
two distinct original residual-gap oscillation margins. -/
structure p4Q2PZ37AFF_originalShellBall
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ) where
  center :
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
  radius : ℝ
  marginLo : ℝ
  marginHi : ℝ
  hRadius : 0 < radius
  hMarginLo : 0 < marginLo
  hMarginHi : 0 < marginHi
  hOrder : lo ≤ hi
  hCenterLo : marginLo <
    p4Q2PZ37AFB_originalResidualGap H e lo center
  hCenterHi :
    p4Q2PZ37AFB_originalResidualGap H e hi center < -marginHi
  hOscLo : ∀ z, p4Q2PZ37ADL_originalFullBoundaryChordalDistance H center z <
    radius →
      |p4Q2PZ37AFB_originalResidualGap H e lo z -
        p4Q2PZ37AFB_originalResidualGap H e lo center| < marginLo
  hOscHi : ∀ z, p4Q2PZ37ADL_originalFullBoundaryChordalDistance H center z <
    radius →
      |p4Q2PZ37AFB_originalResidualGap H e hi z -
        p4Q2PZ37AFB_originalResidualGap H e hi center| < marginHi

/-- The certified genuine boundary ball lies ENTIRELY in the true
shell, not merely in a proxy or independently sampled event. -/
theorem p4Q2PZ37AFF_originalShellBall_subset
    (e : Link) {lo hi : ℝ}
    (w : p4Q2PZ37AFF_originalShellBall H e lo hi) :
    Ball w.center w.radius ⊆ Shell e lo hi := by
  intro z hz
  change D w.center z < w.radius at hz
  have hLow := (abs_lt.mp (w.hOscLo z hz)).1
  have hHigh := (abs_lt.mp (w.hOscHi z hz)).2
  have hLowPos : 0 < Gap e lo z := by
    linarith only [hLow, w.hCenterLo]
  have hHighNeg : Gap e hi z < 0 := by
    linarith only [hHigh, w.hCenterHi]
  refine ⟨(p4Q2PZ37AFF_originalBad_iff_gap_pos
    H e lo z).mpr hLowPos, ?_⟩
  intro hzHigh
  have hBadPos :=
    (p4Q2PZ37AFF_originalBad_iff_gap_pos H e hi z).mp hzHigh
  linarith only [hBadPos, hHighNeg]

/-- The EXACT AEA original pair-Haar radius floor, carried by the
actual shell-ball witness. -/
def p4Q2PZ37AFF_originalShellFloor
    (e : Link) {lo hi : ℝ}
    (w : p4Q2PZ37AFF_originalShellBall H e lo hi) : ℝ :=
  p4Q2PZ37AFD_originalHaarBallFloor H w.radius

/-- Every certified genuine physical shell ball has positive explicit
H-dependent original Haar mass floor. -/
theorem p4Q2PZ37AFF_originalShellFloor_pos
    (e : Link) {lo hi : ℝ}
    (w : p4Q2PZ37AFF_originalShellBall H e lo hi) :
    0 < p4Q2PZ37AFF_originalShellFloor H e w := by
  exact p4Q2PZ37AEA_explicitFloor_pos H w.radius w.hRadius

/-- The positive original AEA floor truly subtracts from the
original shell's pair-Haar mass. -/
theorem p4Q2PZ37AFF_originalShellFloor_le_mass
    (e : Link) {lo hi : ℝ}
    (w : p4Q2PZ37AFF_originalShellBall H e lo hi) :
    p4Q2PZ37AFF_originalShellFloor H e w ≤
      Measure.real outer (Shell e lo hi) := by
  exact (p4Q2PZ37AEA_originalFullBall_mass_ge_explicit
    H w.center w.radius w.hRadius).trans
      (measureReal_mono
        (p4Q2PZ37AFF_originalShellBall_subset H e w)
        (measure_lt_top outer _).ne)

/-- A strictly two-sided residual-gap center yields a TRUE shell ball
by AFB compact uniform continuity. Existence is CONDITIONAL on the
actual original physical signs at the center, never asserted globally. -/
theorem p4Q2PZ37AFF_originalShellBall_exists_of_strictCenter
    (e : Link) (lo hi : ℝ) (hOrder : lo ≤ hi)
    (a : Pair) (hLo : 0 < Gap e lo a) (hHi : Gap e hi a < 0) :
    ∃ w : p4Q2PZ37AFF_originalShellBall H e lo hi,
      w.center = a := by
  let etaLo : ℝ := Gap e lo a / 2
  let etaHi : ℝ := -(Gap e hi a) / 2
  have hpLo : 0 < etaLo := by
    dsimp [etaLo]
    linarith only [hLo]
  have hpHi : 0 < etaHi := by
    dsimp [etaHi]
    linarith only [hHi]
  obtain ⟨rLo, hrLo, hModLo⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e lo etaLo hpLo
  obtain ⟨rHi, hrHi, hModHi⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e hi etaHi hpHi
  refine ⟨{
    center := a
    radius := min rLo rHi
    marginLo := etaLo
    marginHi := etaHi
    hRadius := lt_min hrLo hrHi
    hMarginLo := hpLo
    hMarginHi := hpHi
    hOrder := hOrder
    hCenterLo := by
      dsimp [etaLo]
      linarith only [hLo]
    hCenterHi := by
      dsimp [etaHi]
      linarith only [hHi]
    hOscLo := by
      intro z hz
      exact hModLo a z (lt_of_lt_of_le hz (min_le_left _ _))
    hOscHi := by
      intro z hz
      exact hModHi a z (lt_of_lt_of_le hz (min_le_right _ _))
  }, rfl⟩

/-- Single-shell Haar subtraction, with no double counting. -/
theorem p4Q2PZ37AFF_originalShell_subtractFloor
    (e : Link) {lo hi : ℝ}
    (w : p4Q2PZ37AFF_originalShellBall H e lo hi) :
    Measure.real outer (Bad e hi) +
      p4Q2PZ37AFF_originalShellFloor H e w ≤
        Measure.real outer (Bad e lo) := by
  have hExact :=
    p4Q2PZ37AFF_originalShell_mass_exact H e lo hi w.hOrder
  have hFloor := p4Q2PZ37AFF_originalShellFloor_le_mass H e w
  linarith only [hExact, hFloor]

/-- Balls certified in adjacent true shells cannot overlap, even if
their chosen radii and the two gap moduli are different. -/
theorem p4Q2PZ37AFF_originalAdjacentShellBalls_disjoint
    (e : Link) {lo mid hi : ℝ}
    (w₁ : p4Q2PZ37AFF_originalShellBall H e lo mid)
    (w₂ : p4Q2PZ37AFF_originalShellBall H e mid hi) :
    Disjoint (Ball w₁.center w₁.radius)
      (Ball w₂.center w₂.radius) := by
  refine Set.disjoint_left.mpr ?_
  intro z hz₁ hz₂
  have hLeft := p4Q2PZ37AFF_originalShellBall_subset H e w₁ hz₁
  have hRight := p4Q2PZ37AFF_originalShellBall_subset H e w₂ hz₂
  exact hLeft.2 hRight.1

/-- Exact two-shell telescoping for genuinely nested thresholds. -/
theorem p4Q2PZ37AFF_originalTwoShells_mass_exact
    (e : Link) {lo mid hi : ℝ}
    (w₁ : p4Q2PZ37AFF_originalShellBall H e lo mid)
    (w₂ : p4Q2PZ37AFF_originalShellBall H e mid hi) :
    Measure.real outer (Bad e hi) +
      Measure.real outer (Shell e mid hi) +
      Measure.real outer (Shell e lo mid) =
        Measure.real outer (Bad e lo) := by
  have h₁ := p4Q2PZ37AFF_originalShell_mass_exact
    H e lo mid w₁.hOrder
  have h₂ := p4Q2PZ37AFF_originalShell_mass_exact
    H e mid hi w₂.hOrder
  linarith only [h₁, h₂]

/-- A typed finite chain only accepts a shell whose high threshold is
exactly the low threshold of the remaining chain: no gaps, missing
ordering witnesses or duplicated shell subtraction are possible. -/
inductive p4Q2PZ37AFF_originalShellChain
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    ℝ → ℝ → Type where
  | refl (theta : ℝ) :
      p4Q2PZ37AFF_originalShellChain H e theta theta
  | step {lo mid hi : ℝ}
      (w : p4Q2PZ37AFF_originalShellBall H e lo mid)
      (rest : p4Q2PZ37AFF_originalShellChain H e mid hi) :
      p4Q2PZ37AFF_originalShellChain H e lo hi

/-- Finite sum of strictly positive original AEA floors for typed
adjacent physical shell-ball witnesses. -/
def p4Q2PZ37AFF_originalShellChainFloor
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi) : ℝ :=
  match chain with
  | .refl _ => 0
  | .step w rest =>
      p4Q2PZ37AFF_originalShellFloor H e w +
        p4Q2PZ37AFF_originalShellChainFloor H e rest

/-- The total floor of any finite physical shell chain is nonnegative;
each genuine nonempty step supplies a strictly positive summand. -/
theorem p4Q2PZ37AFF_originalShellChainFloor_nonneg
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi) :
    0 ≤ p4Q2PZ37AFF_originalShellChainFloor H e chain := by
  induction chain with
  | refl theta =>
      change (0 : ℝ) ≤ 0
      exact le_refl _
  | step w rest ih =>
      change (0 : ℝ) ≤
        p4Q2PZ37AFF_originalShellFloor H e w +
          p4Q2PZ37AFF_originalShellChainFloor H e rest
      exact add_nonneg
        (le_of_lt (p4Q2PZ37AFF_originalShellFloor_pos H e w)) ih

/-- Finite telescoping inequality in the ORIGINAL pair-Haar space.
At every step the next bad event is a subset of the previous one and
the chain subtracts only a certified DISJOINT shell floor. -/
theorem p4Q2PZ37AFF_originalShellChain_mass_floor
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi) :
    Measure.real outer (Bad e hi) +
      p4Q2PZ37AFF_originalShellChainFloor H e chain ≤
        Measure.real outer (Bad e lo) := by
  induction chain with
  | refl theta =>
      change Measure.real outer (Bad e theta) + 0 ≤
        Measure.real outer (Bad e theta)
      simp
  | step w rest ih =>
      have hStep := p4Q2PZ37AFF_originalShell_subtractFloor H e w
      change Measure.real outer (Bad e _) +
        (p4Q2PZ37AFF_originalShellFloor H e w +
          p4Q2PZ37AFF_originalShellChainFloor H e rest) ≤
            Measure.real outer (Bad e _) 
      linarith only [hStep, ih]

/-- The genuine refined Haar budget uses a separate valid top AFE
table and a genuine base AFE table minus a typed nonoverlapping
physical shell chain. This is NOT a difference of two upper bounds. -/
def p4Q2PZ37AFF_originalHierarchicalBudget
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e)) : ℝ :=
  min (p4Q2PZ37AFE_multiscaleBudget H e topScales)
    (p4Q2PZ37AFE_multiscaleBudget H e baseScales -
      p4Q2PZ37AFF_originalShellChainFloor H e chain)

/-- Main AFF true hierarchical pair-Haar mass certificate.
Distinct witness thresholds/radii contribute without overlap and
without replacing the actual Wilson/Perron physical law. -/
theorem p4Q2PZ37AFF_originalHierarchicalHaarMass_upper
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hBase : ∀ c ∈ baseScales, c.theta ≤ lo)
    (hTop : ∀ c ∈ topScales, c.theta ≤ hi) :
    Measure.real outer (Bad e hi) ≤
      p4Q2PZ37AFF_originalHierarchicalBudget
        H e chain baseScales topScales := by
  have hb := p4Q2PZ37AFE_multiscaleHaarMass_upper
    H e lo baseScales hBase
  have ht := p4Q2PZ37AFE_multiscaleHaarMass_upper
    H e hi topScales hTop
  have hs := p4Q2PZ37AFF_originalShellChain_mass_floor H e chain
  change Measure.real outer (Bad e hi) ≤
    min (p4Q2PZ37AFE_multiscaleBudget H e topScales)
      (p4Q2PZ37AFE_multiscaleBudget H e baseScales -
        p4Q2PZ37AFF_originalShellChainFloor H e chain)
  apply le_min ht
  linarith only [hb, hs]

/-- AFF is not worse than the original AFE top-threshold table. -/
theorem p4Q2PZ37AFF_originalHierarchicalBudget_le_top
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e)) :
    p4Q2PZ37AFF_originalHierarchicalBudget
      H e chain baseScales topScales ≤
        p4Q2PZ37AFE_multiscaleBudget H e topScales := by
  exact min_le_left _ _

/-- AFF cannot exceed even the original base AFE upper bound. -/
theorem p4Q2PZ37AFF_originalHierarchicalBudget_le_base
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e)) :
    p4Q2PZ37AFF_originalHierarchicalBudget
      H e chain baseScales topScales ≤
        p4Q2PZ37AFE_multiscaleBudget H e baseScales := by
  exact (min_le_right _ _).trans
    (sub_le_self _ (p4Q2PZ37AFF_originalShellChainFloor_nonneg H e chain))

/-- A valid AFF hierarchical budget is in [0,1] as a consequence
of the true original probability mass it bounds. -/
theorem p4Q2PZ37AFF_originalHierarchicalBudget_range
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hBase : ∀ c ∈ baseScales, c.theta ≤ lo)
    (hTop : ∀ c ∈ topScales, c.theta ≤ hi) :
    0 ≤ p4Q2PZ37AFF_originalHierarchicalBudget
        H e chain baseScales topScales ∧
      p4Q2PZ37AFF_originalHierarchicalBudget
        H e chain baseScales topScales ≤ 1 := by
  constructor
  · exact measureReal_nonneg.trans
      (p4Q2PZ37AFF_originalHierarchicalHaarMass_upper
        H e chain baseScales topScales hBase hTop)
  · exact (p4Q2PZ37AFF_originalHierarchicalBudget_le_top
      H e chain baseScales topScales).trans
        (p4Q2PZ37AFE_multiscaleBudget_le_one H e topScales)

/-- A separately verified numerical hierarchical shell certificate
satisfying AFA's unchanged 64 threshold proves the original positive
squared-mean GI certificate. -/
theorem p4Q2PZ37AFF_originalHierarchical_gives_positiveBudget
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hBase : ∀ c ∈ baseScales, c.theta ≤ lo)
    (hTop : ∀ c ∈ topScales, c.theta ≤ hi)
    (hNumeric : hi * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFF_originalHierarchicalBudget
          H e chain baseScales topScales < 64 * A4 e) :
    0 < Budget b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    H e hi
      (p4Q2PZ37AFF_originalHierarchicalBudget
        H e chain baseScales topScales)
    hTheta
    (p4Q2PZ37AFF_originalHierarchicalHaarMass_upper
      H e chain baseScales topScales hBase hTop) hNumeric

/-- The unchanged true signed two-posterior Wilson source GI response
is nonzero on an open positive ORIGINAL pair-Haar region. -/
theorem p4Q2PZ37AFF_originalHierarchical_gives_openGI
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hBase : ∀ c ∈ baseScales, c.theta ≤ lo)
    (hTop : ∀ c ∈ topScales, c.theta ≤ hi)
    (hNumeric : hi * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFF_originalHierarchicalBudget
          H e chain baseScales topScales < 64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e
    (p4Q2PZ37AFF_originalHierarchical_gives_positiveBudget
      H e chain baseScales topScales hTheta hBase hTop hNumeric)

/-- Genuine FC still needs its independent unused original variance
slack, not a substitution of the squared mean GI budget. -/
theorem p4Q2PZ37AFF_originalHierarchicalFC_gives_trueFC
    (e : Link) {lo hi : ℝ} (sigma : ℝ)
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hBase : ∀ c ∈ baseScales, c.theta ≤ lo)
    (hTop : ∀ c ∈ topScales, c.theta ≤ hi)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumeric : (hi + sigma) * A4 e +
      (B b0 hb0)^2 *
        p4Q2PZ37AFF_originalHierarchicalBudget
          H e chain baseScales topScales < 64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    H e hi sigma
      (p4Q2PZ37AFF_originalHierarchicalBudget
        H e chain baseScales topScales)
    hTheta
    (p4Q2PZ37AFF_originalHierarchicalHaarMass_upper
      H e chain baseScales topScales hBase hTop)
    hSlack hNumeric

/-- Obstruction: a failed original squared-mean GI certificate imposes
the original AFA necessary exceptional Haar mass floor on EVERY valid
hierarchical budget. No converse physical gap result is asserted. -/
theorem p4Q2PZ37AFF_nonpositiveBudget_hierarchical_floor
    (e : Link) {lo hi : ℝ}
    (chain : p4Q2PZ37AFF_originalShellChain H e lo hi)
    (baseScales topScales :
      List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ hi)
    (hBase : ∀ c ∈ baseScales, c.theta ≤ lo)
    (hTop : ∀ c ∈ topScales, c.theta ≤ hi)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - hi) * A4 e) / (B b0 hb0)^2 ≤
      p4Q2PZ37AFF_originalHierarchicalBudget
        H e chain baseScales topScales := by
  exact (p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    H e hi hTheta hNonpos).trans
      (p4Q2PZ37AFF_originalHierarchicalHaarMass_upper
        H e chain baseScales topScales hBase hTop)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalBad_iff_gap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShell_measurable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalAdjacentShells_disjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShell_mass_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShellBall_subset
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShellFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShellFloor_le_mass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShellBall_exists_of_strictCenter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShell_subtractFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalAdjacentShellBalls_disjoint
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalTwoShells_mass_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShellChainFloor_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalShellChain_mass_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchicalHaarMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchicalBudget_le_top
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchicalBudget_le_base
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchicalBudget_range
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchical_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchical_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_originalHierarchicalFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFF_nonpositiveBudget_hierarchical_floor
