import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCalibratedChordalHaarBallsV5_PZ37ADK
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ADL — original SU(2) feature injectivity and all-link Haar balls

The original normalized real-eight SU(2) Wilson matrix feature J is
INJECTIVE: all real and imaginary entries of the original matrix are
visible, and the scalar sqrt(1/2) multiplying those coordinates is
NONZERO. Thus ADK's calibrated chordal function d_J is a TRUE metric:
d_J(g,h)=0 if and only if the actual SU(2) holonomies agree.

On the SAME finite interacting Wilson boundary Pair_H=Cfg_H×Cfg_H,
we construct the ALL-LINK chordal ℓ1 metric

  D_H(z,w) = Σ_{e∈Link_H}[d_J(z.left_e,w.left_e)+d_J(z.right_e,w.right_e)]

and verify nonnegativity, identity of indiscernibles, symmetry,
triangle inequality, and continuity in the original product topology.

The full simultaneous finite-coordinate open box

  Q_H(z0,r) = {z : for every ORIGINAL link e, both
    d_J(z0.left_e,z.left_e)<r and d_J(z0.right_e,z.right_e)<r}

has exactly the ORIGINAL boundary pair-Haar product mass.
At numeric r=5/4, existing genuine one-link SU(2) Haar bounds imply

       ν_H(Q_H(z0,5/4)) >= (1/8)^(2*|Link_H|) > 0.

The box lies in a true D_H-open ball of explicit radius
2*|Link_H|*(5/4)+1, and thus that ALL-LINK metric ball has the same
positive H-dependent numeric lower bound. No uncoupled surrogate law
or newly assumed source/covariance regularity is introduced.

This bound decreases exponentially with the true number of spatial
links. It does NOT imply the ADI 1/17 necessary mass filter for the
same all-link ball, and in particular does not prove the strict 68
criterion. The ACI physical nonzero covariance center lies inside
the all-link ball, but its covariance is not proved stable over it.
No H-uniform physical coercivity or continuum Yang--Mills mass gap.
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
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local instance p4Q2PZ37ADL_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ADL_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ADL_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ADL_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ADL_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ADL_probability : IsProbabilityMeasure haar :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The original real-eight feature retains EVERY real and imaginary
entry of the defining complex matrix (indices transposed as in the
existing trace pairing). No abstract kernel embedding is substituted. -/
theorem p4Q2PZ37ADL_complexMatrixRealFeature_injective :
    Function.Injective (complexMatrixRealFeature 2) := by
  intro A B h
  ext i j
  apply Complex.ext
  · have hcoord := congrArg
      (fun v : SpecialUnitaryMatrixRealFeatureSpace 2 =>
        v ((j, i), true)) h
    simpa [complexMatrixRealFeature] using hcoord
  · have hcoord := congrArg
      (fun v : SpecialUnitaryMatrixRealFeatureSpace 2 =>
        v ((j, i), false)) h
    simpa [complexMatrixRealFeature] using hcoord

/-- The genuine normalized SU(2) real-eight matrix feature is injective,
since sqrt(1/2) is nonzero. -/
theorem p4Q2PZ37ADL_trueWilsonFeature_injective :
    Function.Injective (fun g : G => J g) := by
  intro g h h
  have hScale :
      specialUnitaryTwoNormalizedTraceFeatureScale ≠ 0 := by
    unfold specialUnitaryTwoNormalizedTraceFeatureScale
    positivity
  have hReal :
      specialUnitaryMatrixRealFeature 2 g =
        specialUnitaryMatrixRealFeature 2 h := by
    have hCancel := congrArg
      (fun v : SpecialUnitaryMatrixRealFeatureSpace 2 =>
        specialUnitaryTwoNormalizedTraceFeatureScale⁻¹ • v) h
    simpa [specialUnitaryTwoNormalizedTraceFeatureVector, smul_smul,
      hScale] using hCancel
  apply Subtype.ext
  exact p4Q2PZ37ADL_complexMatrixRealFeature_injective hReal

/-- ADK's original Wilson-energy-calibrated chordal function is
a genuine separating metric, not merely a pseudometric. -/
theorem p4Q2PZ37ADL_chordalDistance_eq_zero_iff (g h : G) :
    dJ g h = 0 ↔ g = h := by
  constructor
  · intro hz
    have hVec : J g = J h :=
      sub_eq_zero.mp (norm_eq_zero.mp hz)
    exact p4Q2PZ37ADL_trueWilsonFeature_injective hVec
  · rintro rfl
    exact p4Q2PZ37ADK_trueChordalDistance_self g

theorem p4Q2PZ37ADL_chordalDistance_pos_of_ne
    {g h : G} (hNe : g ≠ h) : 0 < dJ g h := by
  have hZero : dJ g h ≠ 0 := by
    intro hz
    exact hNe ((p4Q2PZ37ADL_chordalDistance_eq_zero_iff g h).mp hz)
  exact lt_of_le_of_ne (p4Q2PZ37ADK_trueChordalDistance_nonneg g h) (Ne.symm hZero)

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
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local instance p4Q2PZ37ADL_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37ADL_sliceProbability : IsProbabilityMeasure slice := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance
local instance p4Q2PZ37ADL_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
  infer_instance

/-- Actual full-slice chordal box, requiring EVERY physical spatial
link coordinate to lie in one genuine SU(2) chordal metric ball. -/
def p4Q2PZ37ADL_originalSliceFullChordalBox
    (a : Cfg) (r : ℝ) : Set Cfg :=
  Set.pi Set.univ (fun e : Link => p4Q2PZ37ADK_trueChordalBall (a e) r)

theorem p4Q2PZ37ADL_sliceBox_center_mem (a : Cfg) (r : ℝ)
    (hr : 0 < r) :
    a ∈ p4Q2PZ37ADL_originalSliceFullChordalBox H a r := by
  intro e _he
  exact p4Q2PZ37ADK_trueChordalBall_mem_center (a e) r hr

/-- Full finite-dimensional product box is genuinely OPEN in the
original SU(2) configuration topology, not a separate discrete topology. -/
theorem p4Q2PZ37ADL_sliceBox_isOpen
    (a : Cfg) (r : ℝ) :
    IsOpen (p4Q2PZ37ADL_originalSliceFullChordalBox H a r) := by
  exact isOpen_set_pi Set.finite_univ
    (fun e _ => p4Q2PZ37ADK_trueChordalBall_isOpen (a e) r)

/-- The SAME genuine finite-product spatial Haar measure of the
whole simultaneous all-link chordal box is the product of the
genuine SU(2) ball masses. -/
theorem p4Q2PZ37ADL_sliceBox_originalHaarMass_eq
    (a : Cfg) (r : ℝ) :
    Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a r) =
      ∏ e : Link, Measure.real haar
        (p4Q2PZ37ADK_trueChordalBall (a e) r) := by
  change Measure.real
      (Measure.pi (fun _ : Link => normalizedCompactHaar G))
      (Set.pi Set.univ (fun e : Link => p4Q2PZ37ADK_trueChordalBall (a e) r)) =
    ∏ e : Link, Measure.real haar (p4Q2PZ37ADK_trueChordalBall (a e) r)
  simp only [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]

/-- NUMERIC H-dependent lower mass for EVERY link at once.
No common physical source or covariance hypothesis is inserted. -/
theorem p4Q2PZ37ADL_sliceBox_originalHaarMass_ge
    (a : Cfg) (r : ℝ) (hr : 1 < r) :
    (1 / 8 : ℝ) ^ Fintype.card Link ≤
      Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a r) := by
  rw [p4Q2PZ37ADL_sliceBox_originalHaarMass_eq]
  calc
    (1 / 8 : ℝ) ^ Fintype.card Link =
        ∏ _e : Link, (1 / 8 : ℝ) := by simp
    _ ≤ ∏ e : Link,
        Measure.real haar (p4Q2PZ37ADK_trueChordalBall (a e) r) :=
      Finset.prod_le_prod
        (fun _ _ => by norm_num)
        (fun e _ => p4Q2PZ37ADK_trueChordalBall_mass_ge_eighth (a e) r hr)

/-- The true simultaneous all-link chordal box has positive original
product-Haar mass for any fixed finite volume and r>1. -/
theorem p4Q2PZ37ADL_sliceBox_originalHaarMass_pos
    (a : Cfg) (r : ℝ) (hr : 1 < r) :
    0 < Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a r) :=
  lt_of_lt_of_le (by positivity)
    (p4Q2PZ37ADL_sliceBox_originalHaarMass_ge H a r hr)

/-- All ORIGINAL spatial links on BOTH adjacent physical boundaries
are simultaneously confined to genuine calibrated SU(2) balls. -/
def p4Q2PZ37ADL_originalFullBoundaryChordalBox
    (a : Pair) (r : ℝ) : Set Pair :=
  p4Q2PZ37ADL_originalSliceFullChordalBox H a.1 r ×ˢ
    p4Q2PZ37ADL_originalSliceFullChordalBox H a.2 r

theorem p4Q2PZ37ADL_originalFullBoundaryBox_isOpen
    (a : Pair) (r : ℝ) :
    IsOpen (p4Q2PZ37ADL_originalFullBoundaryChordalBox H a r) :=
  (p4Q2PZ37ADL_sliceBox_isOpen H a.1 r).prod
    (p4Q2PZ37ADL_sliceBox_isOpen H a.2 r)

theorem p4Q2PZ37ADL_originalFullBoundaryBox_center_mem
    (a : Pair) (r : ℝ) (hr : 0 < r) :
    a ∈ p4Q2PZ37ADL_originalFullBoundaryChordalBox H a r :=
  ⟨p4Q2PZ37ADL_sliceBox_center_mem H a.1 r hr,
   p4Q2PZ37ADL_sliceBox_center_mem H a.2 r hr⟩

/-- The EXACT original Wilson outer pair-Haar all-coordinate box
mass is the product of the TWO genuine full spatial-slice masses. -/
theorem p4Q2PZ37ADL_originalFullBoundaryBox_mass_eq
    (a : Pair) (r : ℝ) :
    Measure.real outer (p4Q2PZ37ADL_originalFullBoundaryChordalBox H a r) =
      Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a.1 r) *
        Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a.2 r) := by
  change Measure.real (slice.prod slice)
      (p4Q2PZ37ADL_originalSliceFullChordalBox H a.1 r ×ˢ
        p4Q2PZ37ADL_originalSliceFullChordalBox H a.2 r) = _
  exact measureReal_prod_prod

/-- Quantitative genuine original all-link/two-boundary floor.
There are exactly 2*card(Link H) ORIGINAL SU(2) coordinates, so
the lower bound is H-dependent; no all-H uniform positive floor. -/
theorem p4Q2PZ37ADL_originalFullBoundaryBox_mass_ge
    (a : Pair) (r : ℝ) (hr : 1 < r) :
    (1 / 8 : ℝ) ^ (2 * Fintype.card Link) ≤
      Measure.real outer (p4Q2PZ37ADL_originalFullBoundaryChordalBox H a r) := by
  rw [p4Q2PZ37ADL_originalFullBoundaryBox_mass_eq]
  have hLeft := p4Q2PZ37ADL_sliceBox_originalHaarMass_ge H a.1 r hr
  have hRight := p4Q2PZ37ADL_sliceBox_originalHaarMass_ge H a.2 r hr
  calc
    (1 / 8 : ℝ) ^ (2 * Fintype.card Link) =
        ((1 / 8 : ℝ) ^ Fintype.card Link) *
          ((1 / 8 : ℝ) ^ Fintype.card Link) := by
      rw [two_mul, pow_add]
    _ ≤ Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a.1 r) *
          Measure.real slice (p4Q2PZ37ADL_originalSliceFullChordalBox H a.2 r) :=
      mul_le_mul hLeft hRight (by positivity) (by positivity)

theorem p4Q2PZ37ADL_originalFullBoundaryBox_mass_pos
    (a : Pair) (r : ℝ) (hr : 1 < r) :
    0 < Measure.real outer (p4Q2PZ37ADL_originalFullBoundaryChordalBox H a r) :=
  lt_of_lt_of_le (by positivity)
    (p4Q2PZ37ADL_originalFullBoundaryBox_mass_ge H a r hr)

/-- A TRUE all-link (ℓ1) chordal metric, summing the original
normalized Wilson-feature distances on both physical boundaries. -/
def p4Q2PZ37ADL_originalFullBoundaryChordalDistance
    (z w : Pair) : ℝ :=
  ∑ e : Link, (dJ (z.1 e) (w.1 e) + dJ (z.2 e) (w.2 e))

theorem p4Q2PZ37ADL_originalFullDistance_nonneg (z w : Pair) :
    0 ≤ p4Q2PZ37ADL_originalFullBoundaryChordalDistance H z w := by
  unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
  apply Finset.sum_nonneg
  intro e _he
  exact add_nonneg
    (p4Q2PZ37ADK_trueChordalDistance_nonneg (z.1 e) (w.1 e))
    (p4Q2PZ37ADK_trueChordalDistance_nonneg (z.2 e) (w.2 e))

theorem p4Q2PZ37ADL_originalFullDistance_self (z : Pair) :
    p4Q2PZ37ADL_originalFullBoundaryChordalDistance H z z = 0 := by
  unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
  simp [p4Q2PZ37ADK_trueChordalDistance_self]

theorem p4Q2PZ37ADL_originalFullDistance_symm (z w : Pair) :
    p4Q2PZ37ADL_originalFullBoundaryChordalDistance H z w =
      p4Q2PZ37ADL_originalFullBoundaryChordalDistance H w z := by
  unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
  apply Finset.sum_congr rfl
  intro e _he
  rw [p4Q2PZ37ADK_trueChordalDistance_symm,
    p4Q2PZ37ADK_trueChordalDistance_symm]

theorem p4Q2PZ37ADL_originalFullDistance_triangle
    (z w u : Pair) :
    p4Q2PZ37ADL_originalFullBoundaryChordalDistance H z u ≤
      p4Q2PZ37ADL_originalFullBoundaryChordalDistance H z w +
        p4Q2PZ37ADL_originalFullBoundaryChordalDistance H w u := by
  unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
  calc
    (∑ e : Link, (dJ (z.1 e) (u.1 e) + dJ (z.2 e) (u.2 e))) ≤
        ∑ e : Link, ((dJ (z.1 e) (w.1 e) + dJ (w.1 e) (u.1 e)) +
          (dJ (z.2 e) (w.2 e) + dJ (w.2 e) (u.2 e))) := by
      apply Finset.sum_le_sum
      intro e _he
      linarith only [
        p4Q2PZ37ADK_trueChordalDistance_triangle (z.1 e) (w.1 e) (u.1 e),
        p4Q2PZ37ADK_trueChordalDistance_triangle (z.2 e) (w.2 e) (u.2 e)]
    _ = (∑ e : Link, (dJ (z.1 e) (w.1 e) + dJ (z.2 e) (w.2 e))) +
        ∑ e : Link, (dJ (w.1 e) (u.1 e) + dJ (w.2 e) (u.2 e)) := by
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e _he
      ring

/-- The all-link chordal ℓ1 distance separates all original
boundary pairs, by injectivity of every TRUE SU(2) link feature. -/
theorem p4Q2PZ37ADL_originalFullDistance_eq_zero_iff
    (z w : Pair) :
    p4Q2PZ37ADL_originalFullBoundaryChordalDistance H z w = 0 ↔
      z = w := by
  constructor
  · intro hZero
    have hEach :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset Link))
        (f := fun e : Link =>
          dJ (z.1 e) (w.1 e) + dJ (z.2 e) (w.2 e))
        (fun e _ => add_nonneg
          (p4Q2PZ37ADK_trueChordalDistance_nonneg (z.1 e) (w.1 e))
          (p4Q2PZ37ADK_trueChordalDistance_nonneg (z.2 e) (w.2 e)))).mp hZero
    apply Prod.ext
    · funext e
      have hz := hEach e (Finset.mem_univ e)
      have hNonneg := p4Q2PZ37ADK_trueChordalDistance_nonneg (z.2 e) (w.2 e)
      apply (p4Q2PZ37ADL_chordalDistance_eq_zero_iff _ _).mp
      linarith [p4Q2PZ37ADK_trueChordalDistance_nonneg (z.1 e) (w.1 e)]
    · funext e
      have hz := hEach e (Finset.mem_univ e)
      have hNonneg := p4Q2PZ37ADK_trueChordalDistance_nonneg (z.1 e) (w.1 e)
      apply (p4Q2PZ37ADL_chordalDistance_eq_zero_iff _ _).mp
      linarith [p4Q2PZ37ADK_trueChordalDistance_nonneg (z.2 e) (w.2 e)]
  · rintro rfl
    exact p4Q2PZ37ADL_originalFullDistance_self H z

/-- A genuine full boundary ℓ1-chordal ball with explicit numeric
H-dependent radius. -/
def p4Q2PZ37ADL_originalFullBoundaryChordalBall
    (a : Pair) (R : ℝ) : Set Pair :=
  {z | p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z < R}

theorem p4Q2PZ37ADL_originalFullDistance_continuous (a : Pair) :
    Continuous (fun z : Pair =>
      p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z) := by
  unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
  apply continuous_finset_sum
  intro e _he
  have hLeft : Continuous (fun z : Pair => dJ (a.1 e) (z.1 e)) := by
    change Continuous (fun z : Pair => ‖J (a.1 e) - J (z.1 e)‖)
    exact (continuous_const.sub
      (p4Q2PZ37ADK_trueFeature_continuous.comp
        ((continuous_apply e).comp continuous_fst))).norm
  have hRight : Continuous (fun z : Pair => dJ (a.2 e) (z.2 e)) := by
    change Continuous (fun z : Pair => ‖J (a.2 e) - J (z.2 e)‖)
    exact (continuous_const.sub
      (p4Q2PZ37ADK_trueFeature_continuous.comp
        ((continuous_apply e).comp continuous_snd))).norm
  exact hLeft.add hRight

theorem p4Q2PZ37ADL_originalFullChordalBall_isOpen
    (a : Pair) (R : ℝ) :
    IsOpen (p4Q2PZ37ADL_originalFullBoundaryChordalBall H a R) :=
  isOpen_lt (p4Q2PZ37ADL_originalFullDistance_continuous H a)
    continuous_const

/-- Every simultaneous all-link radius-r coordinate box lies in a
REAL full-link chordal ℓ1 ball with fully explicit radius
  R_H(r) = 2*(card Link H)*r + 1.
The +1 makes the inclusion strict even when Link is empty. -/
theorem p4Q2PZ37ADL_fullBox_subset_explicitFullBall
    (a : Pair) (r : ℝ) :
    p4Q2PZ37ADL_originalFullBoundaryChordalBox H a r ⊆
      p4Q2PZ37ADL_originalFullBoundaryChordalBall
        H a (2 * (Fintype.card Link : ℝ) * r + 1) := by
  intro z hz
  have hPoint (e : Link) :
      dJ (a.1 e) (z.1 e) + dJ (a.2 e) (z.2 e) ≤ 2 * r := by
    have hl : dJ (a.1 e) (z.1 e) < r := hz.1 e (Set.mem_univ e)
    have hr : dJ (a.2 e) (z.2 e) < r := hz.2 e (Set.mem_univ e)
    linarith
  have hSum :
      p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z ≤
        ∑ _e : Link, (2 * r) := by
    unfold p4Q2PZ37ADL_originalFullBoundaryChordalDistance
    exact Finset.sum_le_sum (fun e _ => hPoint e)
  have hConst :
      (∑ _e : Link, (2 * r)) =
        2 * (Fintype.card Link : ℝ) * r := by
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  change p4Q2PZ37ADL_originalFullBoundaryChordalDistance H a z <
    2 * (Fintype.card Link : ℝ) * r + 1
  linarith only [hSum, hConst]

/-- Completely unconditional, TRUE original-Haar numeric lower bound
for a FULL all-link metric ball, at explicit volume-dependent radius.
A genuine ACI covariance point can be used as its center, but that
does not imply uniform nonzero covariance across the ball. -/
theorem p4Q2PZ37ADL_originalFullBoundaryBall_mass_ge
    (a : Pair) :
    (1 / 8 : ℝ) ^ (2 * Fintype.card Link) ≤
      Measure.real outer
        (p4Q2PZ37ADL_originalFullBoundaryChordalBall H a
          (2 * (Fintype.card Link : ℝ) * (5 / 4) + 1)) := by
  have hBox :=
    p4Q2PZ37ADL_originalFullBoundaryBox_mass_ge
      H a (5 / 4) (by norm_num)
  exact hBox.trans (measureReal_mono
    (p4Q2PZ37ADL_fullBox_subset_explicitFullBall H a (5 / 4)))

theorem p4Q2PZ37ADL_originalFullBoundaryBall_mass_pos
    (a : Pair) :
    0 < Measure.real outer
      (p4Q2PZ37ADL_originalFullBoundaryChordalBall H a
        (2 * (Fintype.card Link : ℝ) * (5 / 4) + 1)) :=
  lt_of_lt_of_le (by positivity)
    (p4Q2PZ37ADL_originalFullBoundaryBall_mass_ge H a)

/-- TRUE ACI centered-source covariance nonzero point is the center
of an all-original-link metric ball with a quantitative positive
pair-Haar lower bound. This makes no false covariance-stability claim. -/
theorem p4Q2PZ37ADL_originalEveryLink_nonzeroCovariance_fullBall
    (e : Link) :
    ∃ a : Pair,
      C b₀ p4Q2PZ37ADC_fixedCoupling_pos.le e a ≠ 0 ∧
      IsOpen (p4Q2PZ37ADL_originalFullBoundaryChordalBall H a
        (2 * (Fintype.card Link : ℝ) * (5 / 4) + 1)) ∧
      (1 / 8 : ℝ) ^ (2 * Fintype.card Link) ≤
        Measure.real outer (p4Q2PZ37ADL_originalFullBoundaryChordalBall
          H a (2 * (Fintype.card Link : ℝ) * (5 / 4) + 1)) := by
  obtain ⟨a, ha⟩ :=
    p4Q2PZ37ACI_centeredEnergyCovariance_nonzero
      H b₀ p4Q2PZ37ADC_fixedCoupling_pos e
        (originalWilsonExplicitIdentityBoundary H)
  exact ⟨a, ha,
    p4Q2PZ37ADL_originalFullChordalBall_isOpen H a _,
    p4Q2PZ37ADL_originalFullBoundaryBall_mass_ge H a⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADL_complexMatrixRealFeature_injective
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADL_trueWilsonFeature_injective
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADL_chordalDistance_eq_zero_iff
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ADL_chordalDistance_pos_of_ne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_sliceBox_center_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_sliceBox_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_sliceBox_originalHaarMass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_sliceBox_originalHaarMass_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_sliceBox_originalHaarMass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBox_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBox_center_mem
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBox_mass_eq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBox_mass_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBox_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullDistance_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullDistance_self
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullDistance_symm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullDistance_triangle
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullDistance_eq_zero_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullDistance_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullChordalBall_isOpen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_fullBox_subset_explicitFullBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBall_mass_ge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalFullBoundaryBall_mass_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ADL_originalEveryLink_nonzeroCovariance_fullBall
