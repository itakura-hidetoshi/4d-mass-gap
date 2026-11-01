import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFullBoundaryChordalMetricV5_PZ37ADL
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADM — genuine all-link chordal covariance uniform modulus
  and radius-parametric ORIGINAL Haar ball mass

The physical source, original Wilson FF receiver, Perron/transfer, two
interacting posteriors and finite-volume pair-Haar law are unchanged.

ADK proved the exact normalized SU(2) matrix chordal calibration
d_J(g,h)^2=2*E(g^-1*h), and ADL proved this chord separates SU(2)
points and its finite left/right-link sum D_H separates all boundary
pairs, with original-Haar ball mass at one coarse H-dependent radius.

ADM improves the quantitative interface in TWO independent directions:

* The genuine normalized SU(2) chordal distance obeys
       d_J(a,g) = d_J(1,a^-1*g)
  by the EXACT Wilson-energy calibration. Hence normalized genuine
  Haar mass of B_J(a,r) is INDEPENDENT of center a for ALL r>0.
  Define the actual one-link radial mass m(r)=μ(B_J(1,r))>0.
  The original pair-Haar full-coordinate product box then has
  EXACT mass m(r)^(2*card(Link_H)), with no substitute probability.

* The actual all-link sum D_H is jointly continuous, separates points,
  and is defined on a compact ORIGINAL boundary-pair space. A compact
  positive-minimum argument for pairs of covariance values separated
  by ε proves an authentic H/e-dependent GLOBAL UNIFORM CONTINUITY
  MODULUS: for every ε>0, some δ>0 satisfies
       D_H(z,w)<δ -> |C_e(z)-C_e(w)|<ε
  for ALL original boundary pairs z,w simultaneously. This is an
  unconditional statement about the ORIGINAL physical centered-source
  Wilson covariance; it supplies no numeric or linear Lipschitz L.

For every R>0 the full D_H OPEN ball contains the full original
coordinate box of radius R/(2*card(Link_H)+1), so it has true mass

  ν_H(B_D(a,R)) >= m(R/(2*card(Link_H)+1))^(2*card(Link_H)) > 0.

At an original ACI nonzero covariance witness a, choosing the
uniform-continuity radius for ε=|C_e(a)|/2 guarantees that the TRUE
full D_H ball supports |C_e(z)|>=|C_e(a)|/2 and the ADE exact
covariance-square moment lower bound with this very ball.
This is genuine physical model gluing, but the radius and one-link
small-ball m(r) are not numerically evaluated.

Crucial: neither a numeric physical Lipschitz coefficient nor the
strict ADH/ADI original GI 68 threshold, H-uniform mass-gap floor,
or continuum 4D Yang--Mills mass gap has been established.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "haar" => normalizedCompactHaar G
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector
local instance p4Q2PZ37ADM_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADM_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADM_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADM_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADM_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADM_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The existing SU(2) Wilson-energy calibration identifies the
chord length at a with that at identity after a GENUINE group
translation, without an unproved isometry hypothesis. -/
theorem p4Q2PZ37ADM_trueChordalDistance_center_translate
    (a g : G) :
    dJ a g = dJ (1 : G) (a⁻¹ * g) := by
  have hOne :
      (1 : G)⁻¹ * (a⁻¹ * g) = a⁻¹ * g := by simp
  have hA :=
    p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy a g
  have hB :=
    p4Q2PZ37ADK_trueChordalDistance_sq_eq_energy (1 : G) (a⁻¹ * g)
  rw [hOne] at hB
  have hA0 := p4Q2PZ37ADK_trueChordalDistance_nonneg a g
  have hB0 := p4Q2PZ37ADK_trueChordalDistance_nonneg (1 : G) (a⁻¹ * g)
  nlinarith only [hA, hB, hA0, hB0]

/-- Genuine chordal ball centered at any a is exactly a Haar-left
translate of the ball at identity; this holds for ANY real r. -/
theorem p4Q2PZ37ADM_trueChordalBall_eq_translatedIdentity
    (a : G) (r : ℝ) :
    p4Q2PZ37ADK_trueChordalBall a r =
      (fun g : G => a⁻¹ * g) ⁻¹'
        p4Q2PZ37ADK_trueChordalBall (1 : G) r := by
  ext g
  change dJ a g < r ↔ dJ (1 : G) (a⁻¹ * g) < r
  rw [p4Q2PZ37ADM_trueChordalDistance_center_translate]

/-- The ACTUAL normalized SU(2) Haar probability is invariant
under the exact original group translation of every feature ball.
No assertion about physical interacting posteriors is made. -/
theorem p4Q2PZ37ADM_trueChordalBall_HaarMass_centerIndependent
    (a : G) (r : ℝ) :
    Measure.real haar (p4Q2PZ37ADK_trueChordalBall a r) =
      Measure.real haar (p4Q2PZ37ADK_trueChordalBall (1 : G) r) := by
  have hp : MeasurePreserving (fun g : G => a⁻¹ * g)
      (normalizedCompactHaar G) (normalizedCompactHaar G) := by
    simpa only [mul_one] using
      (normalizedCompactHaar_measurePreserving_mul_left_right G a⁻¹ (1 : G))
  rw [p4Q2PZ37ADM_trueChordalBall_eq_translatedIdentity]
  simp only [measureReal_def]
  rw [hp.measure_preimage
    (p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) r).measurableSet.nullMeasurableSet]

/-- True original single-link normalized SU(2) Haar radial mass.
This is an actual measure of a calibrated ball, not a free
positive parameter or a replacement analytic model. -/
def p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass (r : ℝ) : ℝ :=
  Measure.real haar (p4Q2PZ37ADK_trueChordalBall (1 : G) r)

/-- The true SU(2) small-ball radial mass is STRICTLY positive for
every r>0, even far below ADK's coarse radius 1. -/
theorem p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass_pos
    (r : ℝ) (hr : 0 < r) :
    0 < p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass r := by
  letI : (normalizedCompactHaar G).IsOpenPosMeasure := by
    unfold normalizedCompactHaar
    infer_instance
  have hOpen := p4Q2PZ37ADK_trueChordalBall_isOpen (1 : G) r
  have hNonempty : (p4Q2PZ37ADK_trueChordalBall (1 : G) r).Nonempty :=
    ⟨(1 : G), p4Q2PZ37ADK_trueChordalBall_mem_center (1 : G) r hr⟩
  exact ENNReal.toReal_pos (hOpen.measure_pos haar hNonempty).ne'
    (measure_ne_top _ _)

/-- Exact, not just estimated, genuine Haar ball mass at every
original SU(2) center is the same radial function. -/
theorem p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial
    (a : G) (r : ℝ) :
    Measure.real haar (p4Q2PZ37ADK_trueChordalBall a r) =
      p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass r :=
  p4Q2PZ37ADM_trueChordalBall_HaarMass_centerIndependent a r

/-- Generic compact-space proof of UNIFORM continuity with respect
to any jointly continuous separating nonnegative distance function.
The bad-pair set {ε ≤ |f(x)-f(y)|} is compact; the distance has
a strictly positive attained minimum on it, including if empty.
This never invokes an arbitrary new topology or Lipschitz axiom. -/
theorem p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (d : X → X → ℝ)
    (hD : Continuous (fun q : X × X => d q.1 q.2))
    (hD0 : ∀ x y, d x y = 0 ↔ x = y)
    (hDpos : ∀ x y, 0 ≤ d x y)
    (f : X → ℝ) (hf : Continuous f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : X,
      d x y < δ → |f x - f y| < ε := by
  let K : Set (X × X) := {q | ε ≤ |f q.1 - f q.2|}
  have hClosed : IsClosed K :=
    isClosed_le continuous_const
      (((hf.comp continuous_fst).sub
        (hf.comp continuous_snd)).abs)
  have hCompact : IsCompact K := hClosed.isCompact
  have hPositive : ∀ q ∈ K, (0 : ℝ) < d q.1 q.2 := by
    intro q hq
    have hNe : q.1 ≠ q.2 := by
      intro hEq
      have hBad : ε ≤ (0 : ℝ) := by
        simpa [K, hEq] using hq
      linarith
    have hNeDist : d q.1 q.2 ≠ 0 := by
      intro hd
      exact hNe ((hD0 q.1 q.2).mp hd)
    exact lt_of_le_of_ne (hDpos q.1 q.2) (Ne.symm hNeDist)
  obtain ⟨δ, hδ, hLower⟩ :=
    hCompact.exists_forall_le' hD.continuousOn hPositive
  refine ⟨δ, hδ, ?_⟩
  intro x y hDist
  by_contra hNot
  have hK : (x, y) ∈ K := by
    change ε ≤ |f x - f y|
    exact le_of_not_gt hNot
  exact (not_lt_of_ge (hLower (x, y) hK)) hDist

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "slice" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "b₀" => p4Q2PZ37ADC_fixedCoupling
local notation "f₀" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Box" => p4Q2PZ37ADL_originalFullBoundaryChordalBox H
local notation "Ball" => p4Q2PZ37ADL_originalFullBoundaryChordalBall H
local notation "m" => p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass
local instance p4Q2PZ37ADM_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADM_pairCompact : CompactSpace Pair := by
  infer_instance
local instance p4Q2PZ37ADM_sliceProbability : IsProbabilityMeasure slice := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ADM_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- The TRUE original finite-volume boundary-pair Haar mass of the
full all-link two-boundary chordal box is an EXACT radial power.
Each genuine Haar factor has the SAME center-independent mass m(r).
No H-uniform positivity is claimed. -/
theorem p4Q2PZ37ADM_originalFullBoxHaarMass_exactRadialPower
    (a : Pair) (r : ℝ) :
    Measure.real outer (Box a r) =
      m r ^ (2 * Fintype.card Link) := by
  rw [p4Q2PZ37ADL_originalFullBoundaryBox_mass_eq,
    p4Q2PZ37ADL_sliceBox_originalHaarMass_eq,
    p4Q2PZ37ADL_sliceBox_originalHaarMass_eq]
  simp_rw [p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial]
  simp only [Finset.prod_const, Finset.card_univ]
  rw [two_mul, pow_add]

/-- Every genuine full coordinate box has positive original pair
Haar mass at EVERY radius r>0, not just the coarse r>1 regime. -/
theorem p4Q2PZ37ADM_originalFullBoxHaarMass_pos_everyRadius
    (a : Pair) (r : ℝ) (hr : 0 < r) :
    0 < Measure.real outer (Box a r) := by
  rw [p4Q2PZ37ADM_originalFullBoxHaarMass_exactRadialPower]
  exact pow_pos (p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass_pos r hr) _

/-- A simultaneous true all-coordinate box of radius r is inside
the genuine full-boundary chordal ℓ1 open ball at ANY radius R
larger than 2*(card physical links)*r. -/
theorem p4Q2PZ37ADM_originalFullBox_subset_ball_of_radius
    (a : Pair) (r R : ℝ)
    (hRadius : 2 * (Fintype.card Link : ℝ) * r < R) :
    Box a r ⊆ Ball a R := by
  intro z hz
  have hPoint (e : Link) :
      dJ (a.1 e) (z.1 e) + dJ (a.2 e) (z.2 e) ≤ 2 * r := by
    have hL : dJ (a.1 e) (z.1 e) < r := hz.1 e (Set.mem_univ e)
    have hR : dJ (a.2 e) (z.2 e) < r := hz.2 e (Set.mem_univ e)
    linarith
  have hSum : D a z ≤ ∑ _e : Link, (2 * r) := by
    unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
    exact Finset.sum_le_sum (fun e _ => hPoint e)
  have hConst : (∑ _e : Link, (2 * r)) =
      2 * (Fintype.card Link : ℝ) * r := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  exact lt_of_le_of_lt (hSum.trans_eq hConst) hRadius

/-- For EVERY genuine positive full-boundary chordal ℓ1 radius R,
an explicit SMALL original Haar box of radius R/(2*card+1)
fits inside the full boundary ball. The total number of coordinates
is the true two-boundary 2*card(Link_H), not an abstract dimension. -/
theorem p4Q2PZ37ADM_originalFullBox_scale_fitsBall
    (a : Pair) (R : ℝ) (hR : 0 < R) :
    Box a (R / (2 * (Fintype.card Link : ℝ) + 1)) ⊆
      Ball a R := by
  have hCard : 0 ≤ (Fintype.card Link : ℝ) := Nat.cast_nonneg _
  have hDen : 0 < 2 * (Fintype.card Link : ℝ) + 1 := by positivity
  apply p4Q2PZ37ADM_originalFullBox_subset_ball_of_radius H
  have hStrict : 2 * (Fintype.card Link : ℝ) * R <
      R * (2 * (Fintype.card Link : ℝ) + 1) := by
    nlinarith only [hR]
  calc
    2 * (Fintype.card Link : ℝ) *
        (R / (2 * (Fintype.card Link : ℝ) + 1)) =
        (2 * (Fintype.card Link : ℝ) * R) /
          (2 * (Fintype.card Link : ℝ) + 1) := by ring
    _ < R := (div_lt_iff₀ hDen).mpr hStrict

/-- Exact model-specific TRUE radial Haar lower bound for ANY genuine
full all-link metric ball radius R>0, including very small R:
  mass >= m(R/(2*n+1))^(2*n)>0
where m is a named, unchanged original normalized SU(2) Haar
measurement, and n is the original actual link count. -/
theorem p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower
    (a : Pair) (R : ℝ) (hR : 0 < R) :
    m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
      Measure.real outer (Ball a R) := by
  rw [← p4Q2PZ37ADM_originalFullBoxHaarMass_exactRadialPower]
  exact measureReal_mono (p4Q2PZ37ADM_originalFullBox_scale_fitsBall H a R hR)

/-- Every original all-link D_H ball at any positive radius
has strictly positive genuine pair-Haar mass; the proof identifies
the precise positive H-dependent radial-power lower bound. -/
theorem p4Q2PZ37ADM_originalFullBall_mass_pos_everyRadius
    (a : Pair) (R : ℝ) (hR : 0 < R) :
    0 < Measure.real outer (Ball a R) := by
  have hCard : 0 ≤ (Fintype.card Link : ℝ) := Nat.cast_nonneg _
  have hDen : 0 < 2 * (Fintype.card Link : ℝ) + 1 := by positivity
  have hr : 0 < R / (2 * (Fintype.card Link : ℝ) + 1) :=
    div_pos hR hDen
  exact (pow_pos
    (p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass_pos _ hr) _).trans_le
      (p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower H a R hR)

/-- The true full ORIGINAL boundary-pair chordal ℓ1 distance
is JOINTLY continuous on the original product topology,
not merely continuous in its second argument at fixed center. -/
theorem p4Q2PZ37ADM_originalFullDistance_jointContinuous :
    Continuous (fun q : Pair × Pair => D q.1 q.2) := by
  unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
  apply continuous_finset_sum
  intro e _he
  have hLL : Continuous (fun q : Pair × Pair => J (q.1.1 e)) :=
    p4Q2PZ37ADK_trueFeature_continuous.comp
      ((continuous_apply e).comp (continuous_fst.comp continuous_fst))
  have hRL : Continuous (fun q : Pair × Pair => J (q.2.1 e)) :=
    p4Q2PZ37ADK_trueFeature_continuous.comp
      ((continuous_apply e).comp (continuous_fst.comp continuous_snd))
  have hLR : Continuous (fun q : Pair × Pair => J (q.1.2 e)) :=
    p4Q2PZ37ADK_trueFeature_continuous.comp
      ((continuous_apply e).comp (continuous_snd.comp continuous_fst))
  have hRR : Continuous (fun q : Pair × Pair => J (q.2.2 e)) :=
    p4Q2PZ37ADK_trueFeature_continuous.comp
      ((continuous_apply e).comp (continuous_snd.comp continuous_snd))
  change Continuous (fun q : Pair × Pair =>
    ‖J (q.1.1 e) - J (q.2.1 e)‖ +
      ‖J (q.1.2 e) - J (q.2.2 e)‖)
  exact (hLL.sub hRL).norm.add (hLR.sub hRR).norm

/-- Original physical centered-source Wilson SU(2) covariance
admits one H/e/ε-dependent UNIFORM modulus in the ACTUAL full
calibrated D_H distance: ALL original boundary pairs x,y obey
the same implication. No Lipschitz constant is hypothesized. -/
theorem p4Q2PZ37ADM_originalCenteredCovariance_uniformChordalModulus
    (e : Link) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z w : Pair, D z w < δ →
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z -
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e w| < ε := by
  have hC : Continuous (fun z : Pair =>
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) :=
    p4Q2PZ37ACD_originalReceiver_covariance_continuous
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos.le f₀ e
  exact p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
    D
    (p4Q2PZ37ADM_originalFullDistance_jointContinuous H)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_eq_zero_iff H z w)
    (fun z w => p4Q2PZ37ADL_originalFullDistance_nonneg H z w)
    (fun z : Pair => C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z)
    hC ε hε

/-- At an ACTUAL ACI original centered-source nonzero covariance
point a, compactness yields one genuine positive full D_H radius
R (in the calibrated ORIGINAL distance) on which EVERY value has
at least half the original covariance amplitude. This is not a
numeric radius or numeric Lipschitz bound. -/
theorem p4Q2PZ37ADM_originalNonzeroCovariance_stableFullBall
    (e : Link) (a : Pair)
    (ha : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ Ball a R,
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2 ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
  let v : ℝ := C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a
  have hAmp : 0 < |v| / 2 :=
    div_pos (abs_pos.mpr ha) (by norm_num)
  obtain ⟨R, hR, hMod⟩ :=
    p4Q2PZ37ADM_originalCenteredCovariance_uniformChordalModulus
      H e (|v| / 2) hAmp
  refine ⟨R, hR, ?_⟩
  intro z hz
  have hD :
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
        C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| < |v| / 2 :=
    hMod a z hz
  have hTriangle :
      |v| ≤
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| +
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
    calc
      |v| = |(C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a -
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z) +
          C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z| := by
            congr 1
            dsimp [v]
            ring
      _ ≤ _ := abs_add_le _ _
  linarith only [hTriangle, hD]

/-- The very same genuinely calibrated full all-link chordal ball
has actual nonzero physical covariance everywhere, true Haar mass
bounded from below by the exact original SU(2) radial-power law,
and the ADE exact physical covariance-square moment lower bound.
The radius is supplied by genuine uniform continuity, not assumed. -/
theorem p4Q2PZ37ADM_originalNonzeroCovariance_radialMomentWitness
    (e : Link) (a : Pair)
    (ha : C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0) :
    ∃ R : ℝ, 0 < R ∧
      0 < m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ∧
      m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
          Measure.real outer (Ball a R) ∧
      (∀ z ∈ Ball a R,
        |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2 ≤
          |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e z|) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        Measure.real outer (Ball a R) ≤
          S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨R, hR, hStable⟩ :=
    p4Q2PZ37ADM_originalNonzeroCovariance_stableFullBall H e a ha
  have hCard : 0 ≤ (Fintype.card Link : ℝ) := Nat.cast_nonneg _
  have hDen : 0 < 2 * (Fintype.card Link : ℝ) + 1 := by positivity
  have hr : 0 < R / (2 * (Fintype.card Link : ℝ) + 1) :=
    div_pos hR hDen
  have hMassPos : 0 < m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
      (2 * Fintype.card Link) :=
    pow_pos (p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass_pos _ hr) _
  have hMass :=
    p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower H a R hR
  have hAmp : 0 <
      |C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2 :=
    div_pos (abs_pos.mpr ha) (by norm_num)
  have hMoment :=
    p4Q2PZ37ADE_originalOpenCovarianceRegion_lowerMoment
      H e (Ball a R)
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2)
      (p4Q2PZ37ADL_originalFullChordalBall_isOpen H a R)
      hAmp hStable
  exact ⟨R, hR, hMassPos, hMass, hStable, hMoment⟩

/-- No external nonzero-point assumption is needed for the SAME
physical centered-Gauss-law FF receiver: ACI constructs it for
EVERY original physical spatial link, at each finite H. -/
theorem p4Q2PZ37ADM_originalEveryLink_radialMomentWitness
    (e : Link) :
    ∃ (a : Pair) (R : ℝ),
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0 ∧
      0 < R ∧
      0 < m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ∧
      m (R / (2 * (Fintype.card Link : ℝ) + 1)) ^
        (2 * Fintype.card Link) ≤
        Measure.real outer (Ball a R) ∧
      (|C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a| / 2) ^ 2 *
        Measure.real outer (Ball a R) ≤
          S b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e := by
  obtain ⟨a, ha⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  obtain ⟨R, hR, hPositive, hFloor, _hStable, hMoment⟩ :=
    p4Q2PZ37ADM_originalNonzeroCovariance_radialMomentWitness H e a ha
  exact ⟨a, R, ha, hR, hPositive, hFloor, hMoment⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADM_trueChordalDistance_center_translate
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADM_trueChordalBall_eq_translatedIdentity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADM_trueChordalBall_HaarMass_centerIndependent
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADM_trueOneLinkChordalHaarRadialMass_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADM_oneLinkChordalBallMass_eq_radial
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADM_compactContinuous_uniformDistanceModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullBoxHaarMass_exactRadialPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullBoxHaarMass_pos_everyRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullBox_subset_ball_of_radius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullBox_scale_fitsBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullBall_mass_ge_radialPower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullBall_mass_pos_everyRadius
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalFullDistance_jointContinuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalCenteredCovariance_uniformChordalModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalNonzeroCovariance_stableFullBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalNonzeroCovariance_radialMomentWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADM_originalEveryLink_radialMomentWitness
