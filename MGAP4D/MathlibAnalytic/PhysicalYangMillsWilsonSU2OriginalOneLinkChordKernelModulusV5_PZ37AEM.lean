import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSqrtDensityOneLinkHarnackV5_PZ37AEL
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEM — original SU(2) chordal variation and kernel bridge

This append-only theorem module works with the SAME original SU(2) Wilson
energy, spatial plaquettes, temporal crossing links, calibrated chordal
feature d_J, and fixed physical coupling beta_0.

The first physical estimate is unconditional:
  |E(a⁻¹*g)-E(a⁻¹*h)| ≤ d_J(g,h).
It follows directly from the original normalized real-eight SU(2) trace
feature, the unit feature norm and Cauchy–Schwarz, not an added regularity
axiom. Summing the true crossing action shows that its change under an
actual one-link replacement is also ≤ d_J(g,h).

The exponential Wilson kernel is 1-Lipschitz in its NONPOSITIVE
Boltzmann exponent. An exact kernel Lipschitz transfer is established
conditional on the remaining SPATIAL Wilson action one-link modulus.
This premise is explicitly stated: it is not claimed to have been proved
here or replaced by AEL's coarse exp(8 beta_0) Harnack bound.

Next obstruction: establish the spatial plaquette local modulus from
the original four-edge holonomy and finite incidence relation.
No modified posterior, independent Haar law, H-uniform coercivity or
continuum mass gap is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "J" => specialUnitaryTwoNormalizedTraceFeatureVector
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2

/-- An exact unit-norm consequence for the original normalized trace feature. -/
theorem p4Q2PZ37AEM_originalTraceFeature_norm_one (a : G) :
    ‖J a‖ = 1 := by
  have hsq := p4Q2PZ37ADK_trueFeature_norm_sq_one a
  nlinarith [norm_nonneg (J a)]

/-- Fundamental physical one-link Lipschitz inequality: the ORIGINAL
SU(2) Wilson plaquette energy, after left multiplication by a fixed
inverse holonomy, is 1-Lipschitz in the ORIGINAL chordal distance d_J.
This is a direct normalized-trace Hilbert-space estimate. -/
theorem p4Q2PZ37AEM_originalRelativeWilsonEnergy_chordLipschitz
    (a g h : G) :
    |E (a⁻¹ * g) - E (a⁻¹ * h)| ≤ dJ g h := by
  have hEnergy (x : G) :
      E (a⁻¹ * x) = 1 - inner ℝ (J a) (J x) := by
    calc
      E (a⁻¹ * x) =
          1 - specialUnitaryNormalizedTraceRelativeKernel 2 a x := by
        rw [specialUnitaryWilsonPlaquetteEnergy_eq]
        rfl
      _ = 1 - inner ℝ (J a) (J x) := by
        rw [specialUnitaryTwoNormalizedTraceRelativeKernel_eq_inner_featureVector]
  calc
    |E (a⁻¹ * g) - E (a⁻¹ * h)| =
        |inner ℝ (J a) (J h - J g)| := by
      rw [hEnergy g, hEnergy h, inner_sub_right]
      congr 1
      ring
    _ ≤ ‖J a‖ * ‖J h - J g‖ := abs_real_inner_le_norm _ _
    _ = dJ g h := by
      rw [p4Q2PZ37AEM_originalTraceFeature_norm_one, one_mul]
      exact norm_sub_rev (J h) (J g)

/-- The real exponential is 1-Lipschitz on (-∞, 0], in the ordered
orientation needed by the original Wilson Boltzmann factor. -/
theorem p4Q2PZ37AEM_real_exp_nonpos_orderedDifference
    (x y : ℝ) (hxy : x ≤ y) (hy : y ≤ 0) :
    Real.exp y - Real.exp x ≤ y - x := by
  have heY : Real.exp y ≤ 1 := by
    calc
      Real.exp y ≤ Real.exp 0 := Real.exp_le_exp.mpr hy
      _ = 1 := Real.exp_zero
  have hLower := Real.add_one_le_exp (x - y)
  have hSub : 1 - Real.exp (x - y) ≤ y - x := by
    linarith only [hLower]
  have hExp : Real.exp x = Real.exp y * Real.exp (x - y) := by
    calc
      Real.exp x = Real.exp (y + (x - y)) := by congr 1; ring
      _ = Real.exp y * Real.exp (x - y) := Real.exp_add _ _
  calc
    Real.exp y - Real.exp x =
        Real.exp y * (1 - Real.exp (x - y)) := by
          rw [hExp]
          ring
    _ ≤ Real.exp y * (y - x) :=
      mul_le_mul_of_nonneg_left hSub (Real.exp_pos _).le
    _ ≤ 1 * (y - x) :=
      mul_le_mul_of_nonneg_right heY (sub_nonneg.mpr hxy)
    _ = y - x := by ring

theorem p4Q2PZ37AEM_real_exp_nonpos_absLipschitz
    (x y : ℝ) (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  rcases le_total x y with hxy | hyx
  · have hmono : Real.exp x ≤ Real.exp y :=
      Real.exp_le_exp.mpr hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hmono),
      abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith only [p4Q2PZ37AEM_real_exp_nonpos_orderedDifference x y hxy hy]
  · have hmono : Real.exp y ≤ Real.exp x :=
      Real.exp_le_exp.mpr hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hmono),
      abs_of_nonneg (sub_nonneg.mpr hyx)]
    exact p4Q2PZ37AEM_real_exp_nonpos_orderedDifference y x hyx hx

/-- Nonnegative Wilson actions have Boltzmann factors whose absolute
difference is at most beta times the action difference. -/
theorem p4Q2PZ37AEM_real_nonnegativeWilsonBoltzmannLipschitz
    (beta x y : ℝ) (hbeta : 0 ≤ beta)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-beta * x) - Real.exp (-beta * y)| ≤
      beta * |x - y| := by
  have hnegX : -beta * x ≤ 0 := by
    have h := mul_nonneg hbeta hx
    linarith only [h]
  have hnegY : -beta * y ≤ 0 := by
    have h := mul_nonneg hbeta hy
    linarith only [h]
  calc
    |Real.exp (-beta * x) - Real.exp (-beta * y)| ≤
        |(-beta * x) - (-beta * y)| :=
      p4Q2PZ37AEM_real_exp_nonpos_absLipschitz _ _ hnegX hnegY
    _ = beta * |x - y| := by
      have hEq : (-beta * x) - (-beta * y) = -beta * (x - y) := by ring
      rw [hEq, abs_mul, abs_neg, abs_of_nonneg hbeta]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "Replace" =>
  periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink H 2
local notation "Cross" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction H 2
local notation "Spatial" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "Action" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "Kernel" =>
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0

local instance p4Q2PZ37AEM_links : Fintype Link := Fintype.ofFinite _

/-- Direct original crossing-energy one-link variation. It is precisely
Lipschitz in the normalized chordal displacement, unlike AEL's coarse
finite-oscillation Harnack estimate. -/
theorem p4Q2PZ37AEM_originalTemporalCrossing_oneLinkChordLipschitz
    (A B : Cfg) (e : Link) (g h : G) :
    |Cross A (Replace B e g) - Cross A (Replace B e h)| ≤ dJ g h := by
  classical
  let Bg := Replace B e g
  let Bh := Replace B e h
  let Fg := fun j : Link => E ((A j)⁻¹ * Bg j)
  let Fh := fun j : Link => E ((A j)⁻¹ * Bh j)
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingAction_eq_finset_sum,
    ← Finset.sum_sub_distrib]
  change |∑ j : Link, (Fg j - Fh j)| ≤ dJ g h
  have hsum : (∑ j : Link, (Fg j - Fh j)) =
      E ((A e)⁻¹ * g) - E ((A e)⁻¹ * h) := by
    rw [Finset.sum_eq_single e]
    · simp [Fg, Fh, Bg, Bh,
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink]
    · intro j _hj hne
      have hBg :
          Bg j = B j :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
          H 2 B e j g hne
      have hBh :
          Bh j = B j :=
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_of_ne
          H 2 B e j h hne
      simp [Fg, Fh, hBg, hBh]
    · simp
  rw [hsum]
  exact p4Q2PZ37AEM_originalRelativeWilsonEnergy_chordLipschitz (A e) g h

/-- Exact bridge: once the ORIGINAL complete Wilson slab action has
one-link modulus C, its ORIGINAL Boltzmann kernel has beta_0*C.
The premise is exposed, not silently assumed. -/
theorem p4Q2PZ37AEM_originalOneSlabKernel_chordLipschitz_of_action
    (A B : Cfg) (e : Link) (g h : G)
    (C : ℝ) (hAction :
      |Action A (Replace B e g) - Action A (Replace B e h)| ≤
        C * dJ g h) :
    |Kernel A (Replace B e g) - Kernel A (Replace B e h)| ≤
      b0 * C * dJ g h := by
  have hAg : 0 ≤ Action A (Replace B e g) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) _ _
  have hAh : 0 ≤ Action A (Replace B e h) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
      H 2 (by norm_num) _ _
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  calc
    |Real.exp (-b0 * Action A (Replace B e g)) -
      Real.exp (-b0 * Action A (Replace B e h))| ≤
        b0 * |Action A (Replace B e g) - Action A (Replace B e h)| :=
      p4Q2PZ37AEM_real_nonnegativeWilsonBoltzmannLipschitz
        b0 _ _ p4Q2PZ37ADC_fixedCoupling_pos.le hAg hAh
    _ ≤ b0 * (C * dJ g h) :=
      mul_le_mul_of_nonneg_left hAction p4Q2PZ37ADC_fixedCoupling_pos.le
    _ = b0 * C * dJ g h := by ring

/-- Decompose the one-link complete action difference into its physically
proved crossing modulus (=1) and the still-needed spatial modulus (c).
This conditional result isolates the ONLY new local physical lemma
needed to close the original one-slab kernel estimate. -/
theorem p4Q2PZ37AEM_originalOneSlabKernel_chordLipschitz_of_spatial
    (A B : Cfg) (e : Link) (g h : G)
    (c : ℝ) (hc : 0 ≤ c)
    (hSpatial :
      |Spatial (Replace B e g) - Spatial (Replace B e h)| ≤
        c * dJ g h) :
    |Kernel A (Replace B e g) - Kernel A (Replace B e h)| ≤
      b0 * (1 + c / 2) * dJ g h := by
  let Bg := Replace B e g
  let Bh := Replace B e h
  have hCoeff : 0 ≤ 1 + c / 2 := by linarith only [hc]
  have hCross :
      |Cross A Bg - Cross A Bh| ≤ dJ g h :=
    p4Q2PZ37AEM_originalTemporalCrossing_oneLinkChordLipschitz H A B e g h
  have hAction :
      |Action A Bg - Action A Bh| ≤ (1 + c / 2) * dJ g h := by
    have heq :
        Action A Bg - Action A Bh =
          (Cross A Bg - Cross A Bh) +
          (1 / 2 : ℝ) * (Spatial Bg - Spatial Bh) := by
      unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
      ring
    rw [heq]
    calc
      |(Cross A Bg - Cross A Bh) +
        (1 / 2 : ℝ) * (Spatial Bg - Spatial Bh)| ≤
        |Cross A Bg - Cross A Bh| +
          |(1 / 2 : ℝ) * (Spatial Bg - Spatial Bh)| :=
        abs_add_le _ _
      _ = |Cross A Bg - Cross A Bh| +
          (1 / 2 : ℝ) * |Spatial Bg - Spatial Bh| := by
        rw [abs_mul]
        norm_num
      _ ≤ dJ g h + (1 / 2 : ℝ) * (c * dJ g h) := by
        gcongr
      _ = (1 + c / 2) * dJ g h := by ring
  exact p4Q2PZ37AEM_originalOneSlabKernel_chordLipschitz_of_action
    H A B e g h (1 + c / 2) hAction

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalTraceFeature_norm_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_originalRelativeWilsonEnergy_chordLipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_real_exp_nonpos_orderedDifference
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_real_exp_nonpos_absLipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEM_real_nonnegativeWilsonBoltzmannLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalTemporalCrossing_oneLinkChordLipschitz
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalOneSlabKernel_chordLipschitz_of_action
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEM_originalOneSlabKernel_chordLipschitz_of_spatial
