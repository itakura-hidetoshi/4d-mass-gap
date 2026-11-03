import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalDualHaarGreedyPackingV5_PZ37AFD
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFE — finite multi-scale true exceptional pair-Haar certificates

AFD proves for any actual fixed-H Wilson/Perron boundary-pair net and its
greedy separated good packing the original dual estimate

 nu_H(Bad_theta) <= min( sum_flagged nu_H(B_D(a,r)),
                         1-card(goodPacking)*kappa_H(r)).

AFE allows a finite LIST of independently certified, GENUINE original
scales with their own theta_i, eta_i, radius_i, finite original net_i,
and selected good packing_i. For any target theta with theta_i<=theta
for each scale, the exact genuine exception is antitone in theta:

 Bad_theta subset Bad_theta_i.

The proof relies on squared original physical receiver amplitude >= 0.
Consequently the true pair-Haar exception obeys the MINIMUM across
all certified dual budgets, with the empty list returning the genuine
probability ceiling 1. No source, original transfer, Perron weighting,
outer Haar probability, metric, FC envelope or threshold is changed.

A generic finite-list min lemma proves soundness, and a separate
member lemma proves the selected table bound is never larger than
ANY entry. Per-scale valid witnesses exist at fixed H for every
positive guard eta by AFB uniform continuity, AEE finite nets,
and AFD finite greedy good packing. They are NOT numerically small
and do NOT prove H-uniform estimates.

The resulting table is plugged into AFA's unchanged original mean
GI and independent FC-slack threshold, and its converse obstruction.
AEX's conservative two-ball FC no-go remains intact. No continuum
4D Yang--Mills mass gap or physical Hamiltonian gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Universal finite multiscale min soundness. Every entry is an
independently valid upper certificate, and the initial upper bound
also remains valid if there are no entries. -/
theorem p4Q2PZ37AFE_listFoldMin_upper
    {ι : Type*} (xs : List ι) (f : ι → ℝ) (mass : ℝ) :
    ∀ init : ℝ, mass ≤ init →
      (∀ x ∈ xs, mass ≤ f x) →
      mass ≤ xs.foldl (fun acc x => min acc (f x)) init := by
  induction xs with
  | nil =>
      intro init hInit _hEach
      simpa using hInit
  | cons x xs ih =>
      intro init hInit hEach
      change mass ≤ xs.foldl (fun acc y => min acc (f y))
        (min init (f x))
      apply ih (min init (f x))
      · exact le_min hInit (hEach x (by simp))
      · intro y hy
        exact hEach y (by simp [hy])

/-- Adding entries to a finite multiscale min cannot increase its
value beyond the starting ceiling. -/
theorem p4Q2PZ37AFE_listFoldMin_le_initial
    {ι : Type*} (xs : List ι) (f : ι → ℝ) :
    ∀ init : ℝ,
      xs.foldl (fun acc x => min acc (f x)) init ≤ init := by
  induction xs with
  | nil =>
      intro init
      exact le_refl _
  | cons x xs ih =>
      intro init
      change xs.foldl (fun acc y => min acc (f y))
        (min init (f x)) ≤ init
      exact (ih (min init (f x))).trans (min_le_left _ _)

/-- The finite-list minimum is never larger than ANY of its entries;
the table may contain repeated radii or repeated thresholds. -/
theorem p4Q2PZ37AFE_listFoldMin_le_mem
    {ι : Type*} (xs : List ι) (f : ι → ℝ) (c : ι) :
    ∀ init : ℝ, c ∈ xs →
      xs.foldl (fun acc x => min acc (f x)) init ≤ f c := by
  induction xs with
  | nil =>
      intro init hc
      simp at hc
  | cons x xs ih =>
      intro init hc
      rcases List.mem_cons.mp hc with h | h
      · subst x
        change xs.foldl (fun acc y => min acc (f y))
          (min init (f c)) ≤ f c
        exact (p4Q2PZ37AFE_listFoldMin_le_initial xs f
          (min init (f c))).trans (min_le_right _ _)
      · change xs.foldl (fun acc y => min acc (f y))
          (min init (f x)) ≤ f c
        exact ih (min init (f x)) h

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFE_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFE_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFE_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFE_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFE_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFE_probabilityG : IsProbabilityMeasure mu :=
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
local notation "Good" => p4Q2PZ37AFC_originalGoodCenters H
local notation "A4" => p4Q2PZ37AEZ_originalWeightedTransferFourMoment H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "Eunused" => p4Q2PZ37AEY_originalFCUnusedVariance H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H

local instance p4Q2PZ37AFE_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFE_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Each entry retains FULL original physical evidence for its own
theta, guard eta, D_H net radius, flagged samples and selected
greedy good packing, rather than a merely claimed numeric upper bound. -/
structure p4Q2PZ37AFE_originalScale
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H) where
  theta : ℝ
  eta : ℝ
  r : ℝ
  s : Finset (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
  t : Finset (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
  hR : 0 < r
  hNet : p4Q2PZ37AEE_isOriginalFullNet H s r
  hOsc : ∀ a z : (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
    PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2),
    p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z < r →
      |p4Q2PZ37AFB_originalResidualGap H e theta z -
       p4Q2PZ37AFB_originalResidualGap H e theta a| < eta
  hGood : t ⊆ p4Q2PZ37AFC_originalGoodCenters H e s theta eta
  hSep : ∀ a ∈ t, ∀ b ∈ t, a ≠ b →
    2 * r ≤ p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a b

/-- The exact AFD original pair-Haar upper budget of one certified
physical scale, not a surrogate independent Haar probability. -/
def p4Q2PZ37AFE_scaleBudget
    (e : Link) (c : p4Q2PZ37AFE_originalScale H e) : ℝ :=
  p4Q2PZ37AFD_originalDualExceptionalHaarBudget
    H e c.s c.t c.theta c.eta c.r

/-- The actual strict residual exception shrinks when its threshold
increases, because its true physical four-mode amplitude is squared. -/
theorem p4Q2PZ37AFE_originalBad_antitone
    (e : Link) (small target : ℝ) (hSmall : small ≤ target) :
    Bad e target ⊆ Bad e small := by
  intro z hz
  change target * (A b0 hb0 e z)^2 < Wz b0 hb0 e z at hz
  change small * (A b0 hb0 e z)^2 < Wz b0 hb0 e z
  have hMul :
      small * (A b0 hb0 e z)^2 ≤
        target * (A b0 hb0 e z)^2 :=
    mul_le_mul_of_nonneg_right hSmall (sq_nonneg _)
  exact lt_of_le_of_lt hMul hz

/-- Any valid true physical scale at a SMALLER threshold controls
the original bad set at a larger target threshold. -/
theorem p4Q2PZ37AFE_singleScale_controlsTarget
    (e : Link) (target : ℝ)
    (c : p4Q2PZ37AFE_originalScale H e)
    (hBelow : c.theta ≤ target) :
    Measure.real outer (Bad e target) ≤
      p4Q2PZ37AFE_scaleBudget H e c := by
  have hIncl : Bad e target ⊆ Bad e c.theta :=
    p4Q2PZ37AFE_originalBad_antitone H e c.theta target hBelow
  have hMeasure :
      Measure.real outer (Bad e target) ≤
        Measure.real outer (Bad e c.theta) :=
    measureReal_mono hIncl (measure_lt_top outer _).ne
  exact hMeasure.trans
    (p4Q2PZ37AFD_originalDualExceptionalHaarMass_upper
      H e c.s c.t c.theta c.eta c.r
      c.hR c.hNet c.hOsc c.hGood c.hSep)

/-- Different thresholds, margins, radii, genuine finite nets and
finite greedy separated packings may all occur in one finite list.
An empty list gives the literal probability ceiling 1. -/
def p4Q2PZ37AFE_multiscaleBudget
    (e : Link) (scales : List (p4Q2PZ37AFE_originalScale H e)) : ℝ :=
  scales.foldl (fun acc c => min acc
    (p4Q2PZ37AFE_scaleBudget H e c)) 1

/-- The entire finite multiscale table is an upper bound for the SAME
original exceptional pair-Haar event. The only inter-scale condition
is the exact monotonicity theta_i <= target theta. -/
theorem p4Q2PZ37AFE_multiscaleHaarMass_upper
    (e : Link) (target : ℝ)
    (scales : List (p4Q2PZ37AFE_originalScale H e))
    (hBelow : ∀ c ∈ scales, c.theta ≤ target) :
    Measure.real outer (Bad e target) ≤
      p4Q2PZ37AFE_multiscaleBudget H e scales := by
  change Measure.real outer (Bad e target) ≤
    scales.foldl (fun acc c =>
      min acc (p4Q2PZ37AFE_scaleBudget H e c)) 1
  apply p4Q2PZ37AFE_listFoldMin_upper scales
    (p4Q2PZ37AFE_scaleBudget H e)
    (Measure.real outer (Bad e target)) 1
  · have hOne :
        Measure.real outer (Bad e target) ≤
          Measure.real outer (Set.univ : Set Pair) :=
      measureReal_mono (Set.subset_univ _) (measure_lt_top outer _).ne
    simpa only [probReal_univ] using hOne
  · intro c hc
    exact p4Q2PZ37AFE_singleScale_controlsTarget
      H e target c (hBelow c hc)

/-- The multiscale table is never numerically WORSE than any of its
individual genuine Haar certificates, including repeated scales. -/
theorem p4Q2PZ37AFE_multiscaleBudget_le_each
    (e : Link) (scales : List (p4Q2PZ37AFE_originalScale H e))
    (c : p4Q2PZ37AFE_originalScale H e)
    (hc : c ∈ scales) :
    p4Q2PZ37AFE_multiscaleBudget H e scales ≤
      p4Q2PZ37AFE_scaleBudget H e c := by
  exact p4Q2PZ37AFE_listFoldMin_le_mem scales
    (p4Q2PZ37AFE_scaleBudget H e) c 1 hc

/-- A multiscale budget is never larger than the true probability
ceiling one, whether the table is empty or not. -/
theorem p4Q2PZ37AFE_multiscaleBudget_le_one
    (e : Link) (scales : List (p4Q2PZ37AFE_originalScale H e)) :
    p4Q2PZ37AFE_multiscaleBudget H e scales ≤ 1 :=
  p4Q2PZ37AFE_listFoldMin_le_initial scales
    (p4Q2PZ37AFE_scaleBudget H e) 1

/-- Valid multi-scale budgets are nonnegative as a consequence of
their actual Haar-event upper bound, not an assumed interval. -/
theorem p4Q2PZ37AFE_multiscaleBudget_nonneg
    (e : Link) (target : ℝ)
    (scales : List (p4Q2PZ37AFE_originalScale H e))
    (hBelow : ∀ c ∈ scales, c.theta ≤ target) :
    0 ≤ p4Q2PZ37AFE_multiscaleBudget H e scales := by
  exact measureReal_nonneg.trans
    (p4Q2PZ37AFE_multiscaleHaarMass_upper
      H e target scales hBelow)

/-- Each target threshold and positive margin admits an ACTUAL finite
physical-scale certificate by AFB's compact modulus, AEE's true net
and AFD's constructive greedy good-packing selection. No useful
numerical budget upper estimate follows from mere existence. -/
theorem p4Q2PZ37AFE_originalScale_exists
    (e : Link) (theta eta : ℝ) (hEta : 0 < eta) :
    ∃ c : p4Q2PZ37AFE_originalScale H e,
      c.theta = theta ∧ c.eta = eta := by
  obtain ⟨r, hr, hOsc⟩ :=
    p4Q2PZ37AFB_originalResidualGap_uniformChordalModulus
      H e theta eta hEta
  obtain ⟨s, hNet⟩ :=
    p4Q2PZ37AEE_originalFullFiniteNet_exists H r hr
  obtain ⟨t, hGood, hSep, _hCover⟩ :=
    p4Q2PZ37AFD_originalGreedyGoodPacking_exists
      H e s theta eta r hr
  exact ⟨{
    theta := theta
    eta := eta
    r := r
    s := s
    t := t
    hR := hr
    hNet := hNet
    hOsc := hOsc
    hGood := hGood
    hSep := hSep
  }, rfl, rfl⟩

/-- The old true AFA squared mean-GI condition needs only the BEST
of all physically certified multi-radius and multi-threshold entries.
No artificial pointwise transfer ratio or independent Haar sampling. -/
theorem p4Q2PZ37AFE_multiscale_gives_positiveBudget
    (e : Link) (target : ℝ)
    (scales : List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ target)
    (hBelow : ∀ c ∈ scales, c.theta ≤ target)
    (hNumeric : target * A4 e +
      (B b0 hb0)^2 * p4Q2PZ37AFE_multiscaleBudget H e scales <
        64 * A4 e) :
    0 < Budget b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMass_gives_positiveBudget
    H e target (p4Q2PZ37AFE_multiscaleBudget H e scales)
    hTheta
    (p4Q2PZ37AFE_multiscaleHaarMass_upper H e target scales hBelow)
    hNumeric

/-- The same original mean-GI multiscale certificate produces the
existing actual signed two-posterior open positive-Haar region. -/
theorem p4Q2PZ37AFE_multiscale_gives_openGI
    (e : Link) (target : ℝ)
    (scales : List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ target)
    (hBelow : ∀ c ∈ scales, c.theta ≤ target)
    (hNumeric : target * A4 e +
      (B b0 hb0)^2 * p4Q2PZ37AFE_multiscaleBudget H e scales <
        64 * A4 e) :
    ∃ T : Set Pair, IsOpen T ∧ 0 < Measure.real outer T ∧
      ∀ z ∈ T,
        0 < |p4Q2GI_originalWilsonSignedSourceTwoPosteriorExpectationGap
          H b0 hb0 f0 e z| := by
  exact p4Q2PZ37ACO_originalGIBudget_gives_open_positiveGIRegion H b0 hb0 e
    (p4Q2PZ37AFE_multiscale_gives_positiveBudget
      H e target scales hTheta hBelow hNumeric)

/-- The STRICT actual original full-moment FC test additionally needs
a SEPARATELY certified physical unused-variance slack sigma, as in AFA. -/
theorem p4Q2PZ37AFE_multiscaleFC_gives_trueFC
    (e : Link) (target sigma : ℝ)
    (scales : List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ target)
    (hBelow : ∀ c ∈ scales, c.theta ≤ target)
    (hSlack : Eunused e ≤ sigma * A4 e)
    (hNumeric : (target + sigma) * A4 e +
      (B b0 hb0)^2 * p4Q2PZ37AFE_multiscaleBudget H e scales <
        64 * A4 e) :
    (B b0 hb0)^2 < 272 * S b0 hb0 e := by
  exact p4Q2PZ37AFA_originalExceptionalMassFC_gives_trueFC
    H e target sigma (p4Q2PZ37AFE_multiscaleBudget H e scales)
    hTheta
    (p4Q2PZ37AFE_multiscaleHaarMass_upper H e target scales hBelow)
    hSlack hNumeric

/-- A nonpositive true mean GI certificate obstructs EVERY valid
finite multiscale upper budget by the original AFA necessary mass
floor; no GI vanishing or physical mass gap is claimed. -/
theorem p4Q2PZ37AFE_nonpositiveBudget_multiscale_floor
    (e : Link) (target : ℝ)
    (scales : List (p4Q2PZ37AFE_originalScale H e))
    (hTheta : 0 ≤ target)
    (hBelow : ∀ c ∈ scales, c.theta ≤ target)
    (hNonpos : Budget b0 hb0 e ≤ 0) :
    ((64 - target) * A4 e) / (B b0 hb0)^2 ≤
      p4Q2PZ37AFE_multiscaleBudget H e scales := by
  exact (p4Q2PZ37AFA_nonpositiveBudget_exceptionalMass_floor
    H e target hTheta hNonpos).trans
      (p4Q2PZ37AFE_multiscaleHaarMass_upper
        H e target scales hBelow)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFE_listFoldMin_upper
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFE_listFoldMin_le_initial
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFE_listFoldMin_le_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_originalBad_antitone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_singleScale_controlsTarget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscaleHaarMass_upper
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscaleBudget_le_each
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscaleBudget_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscaleBudget_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_originalScale_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscale_gives_positiveBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscale_gives_openGI
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_multiscaleFC_gives_trueFC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFE_nonpositiveBudget_multiscale_floor
