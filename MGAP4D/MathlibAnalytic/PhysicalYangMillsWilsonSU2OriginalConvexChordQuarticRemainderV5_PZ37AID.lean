import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredBoltzmannFactorizationV5_PZ37AIC
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AID — original-kernel convex-chord quartic remainder tightening

Keep the SAME original complete Wilson action, BOTH spatial halfweights,
signed ZW source, product Haar, physical L2 transfer, and AIC's actual
factored error Rc4 and cubic center Pc3.

For EVERY real x, exponential convexity and an explicit derivative comparison
on [0,1] give 0 <= r4(x) <= (4+exp(-x))*x^4/120.
There is no sign restriction or smallness assumption on x.
After exact factorization, the new weight is the genuine kernel mixture
qChord=(4*exp(-beta*a)+K_beta)/5.
Both source-sign weighted centered quartic integrals are retained.
The SAME error and physical transfer inherit their chord intervals for
EVERY real beta, including beta=0 and negative beta.

At beta>=0, qChord<=AIC's min-action weight, strictly pointwise when
beta>0 and Y!=0. Each new correlated moment is at most its old counterpart,
and the new transfer interval is contained in the old AIC interval.
Strict integrated improvement is not claimed.

The exact normalized weight is (4+exp(-beta*Y))/5 for every real beta.
The positive-source margin is equivalent after cancelling the positive outer
exponential. On f>=0, Y is in [-p,3p/2], yielding the one-sided cap
p^4*max((4+exp(beta*p))/5,81/16) at beta>=0.
Integration uses ONLY the original unweighted positive half-mass.
The resulting support budget is an UPPER bound, not a symmetric error bound.

Fixed original beta0 wrappers keep the genuine or support-budget margin
explicit. No actual margin witness, unconditional physical sign, positive/
negative shells, volume-uniform coercivity, Hamiltonian gap or continuum
Yang-Mills gap is claimed. All old definitions, histories, roots, pins and
workflows remain unchanged; this is one appended Lean leaf.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The exact cubic exponential remainder is bounded using the two actual
endpoint exponentials. The coefficients 4/5 and 1/5 are retained. -/
theorem p4Q2PZ37AID_expCubicRemainder_chordUpper (x : ℝ) :
    p4Q2PZ37AIC_expCubicRemainder x ≤
      (4 + Real.exp (-x)) * x ^ 4 / 120 := by
  let F : ℝ → ℝ := fun s =>
    Real.exp (-(s * x)) *
      (1 - (1 - s) * x + ((1 - s) * x) ^ 2 / 2 -
        ((1 - s) * x) ^ 3 / 6)
  let B : ℝ → ℝ := fun s =>
    (1 - x + x ^ 2 / 2 - x ^ 3 / 6) +
      (x ^ 4 / 6) *
        (((1 - Real.exp (-x)) / 5) * (1 - (1 - s) ^ 5) +
          (Real.exp (-x) / 4) * (1 - (1 - s) ^ 4))
  have hSub (t : ℝ) :
      HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
    simpa using (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have hU (t : ℝ) :
      HasDerivAt (fun s : ℝ => (1 - s) * x) (-x) t := by
    simpa using (hSub t).mul (hasDerivAt_const t x)
  have hDerivF (t : ℝ) :
      HasDerivAt F
        ((x ^ 4 / 6) * (1 - t) ^ 3 * Real.exp (-(t * x))) t := by
    dsimp [F]
    convert (((hasDerivAt_id t).mul (hasDerivAt_const t x)).neg.exp).mul
      ((((hasDerivAt_const t (1 : ℝ)).sub (hU t)).add
        (((hU t).pow 2).div_const (2 : ℝ))).sub
          (((hU t).pow 3).div_const (6 : ℝ))) using 1
    simp
    ring
  have hDerivB (t : ℝ) :
      HasDerivAt B
        ((x ^ 4 / 6) * (1 - t) ^ 3 *
          ((1 - t) + t * Real.exp (-x))) t := by
    dsimp [B]
    convert (hasDerivAt_const t
      (1 - x + x ^ 2 / 2 - x ^ 3 / 6)).add
      ((hasDerivAt_const t (x ^ 4 / 6)).mul
        (((hasDerivAt_const t ((1 - Real.exp (-x)) / 5)).mul
          ((hasDerivAt_const t (1 : ℝ)).sub ((hSub t).pow 5))).add
            ((hasDerivAt_const t (Real.exp (-x) / 4)).mul
              ((hasDerivAt_const t (1 : ℝ)).sub ((hSub t).pow 4))))) using 1
    simp
    ring
  have hContF : Continuous F := by
    dsimp [F]
    fun_prop
  have hContB : Continuous B := by
    dsimp [B]
    fun_prop
  have hEnd : F 1 ≤ B 1 := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (B := B)
      (B' := fun t : ℝ =>
        (x ^ 4 / 6) * (1 - t) ^ 3 * ((1 - t) + t * Real.exp (-x)))
      hContF.continuousOn
      (fun t _ => (hDerivF t).hasDerivWithinAt)
      (by dsimp [F, B]; norm_num)
      hContB.continuousOn
      (fun t _ => (hDerivB t).hasDerivWithinAt)
      (fun t ht => ?_)
      ⟨by norm_num, le_rfl⟩
    have hChord : Real.exp (-(t * x)) ≤ (1 - t) + t * Real.exp (-x) := by
      have h := convexOn_exp.2
        (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-x))
        (sub_nonneg.mpr ht.2.le) ht.1 (by ring)
      simpa only [smul_eq_mul, mul_zero, zero_add,
        Real.exp_zero, mul_one, mul_neg] using h
    have hCoeff : 0 ≤ (x ^ 4 / 6) * (1 - t) ^ 3 :=
      mul_nonneg (div_nonneg (by positivity) (by norm_num))
        (pow_nonneg (sub_nonneg.mpr ht.2.le) 3)
    exact mul_le_mul_of_nonneg_left hChord hCoeff
  have hEnd' :
      Real.exp (-x) ≤
        (1 - x + x ^ 2 / 2 - x ^ 3 / 6) +
          (x ^ 4 / 6) * ((1 - Real.exp (-x)) / 5 + Real.exp (-x) / 4) := by
    simpa [F, B] using hEnd
  unfold p4Q2PZ37AIC_expCubicRemainder
  calc
    Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6) ≤
        ((1 - x + x ^ 2 / 2 - x ^ 3 / 6) +
          (x ^ 4 / 6) * ((1 - Real.exp (-x)) / 5 + Real.exp (-x) / 4)) -
            (1 - x + x ^ 2 / 2 - x ^ 3 / 6) :=
      sub_le_sub_right hEnd' _
    _ = (4 + Real.exp (-x)) * x ^ 4 / 120 := by ring

/-- Pair the chord upper bound with AIC's nonnegativity of the same remainder. -/
theorem p4Q2PZ37AID_expCubicRemainder_chordInterval (x : ℝ) :
    0 ≤ p4Q2PZ37AIC_expCubicRemainder x ∧
      p4Q2PZ37AIC_expCubicRemainder x ≤
        (4 + Real.exp (-x)) * x ^ 4 / 120 :=
  ⟨(p4Q2PZ37AIC_expCubicRemainder_interval x).1,
    p4Q2PZ37AID_expCubicRemainder_chordUpper x⟩

/-- Multiplication by the original outer factor retains the actual full
kernel exponential in the improved weight. Valid for every real beta. -/
theorem p4Q2PZ37AID_expCubicRemainder_factoredChordInterval
    (beta a y : ℝ) :
    0 ≤ Real.exp (-beta * a) * p4Q2PZ37AIC_expCubicRemainder (beta * y) ∧
      Real.exp (-beta * a) * p4Q2PZ37AIC_expCubicRemainder (beta * y) ≤
        (4 * Real.exp (-beta * a) + Real.exp (-beta * (a + y))) *
          beta ^ 4 * y ^ 4 / 120 := by
  have hr := p4Q2PZ37AID_expCubicRemainder_chordInterval (beta * y)
  have hExp :
      Real.exp (-beta * a) * Real.exp (-(beta * y)) =
        Real.exp (-beta * (a + y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  refine ⟨mul_nonneg (Real.exp_pos _).le hr.1, ?_⟩
  calc
    Real.exp (-beta * a) * p4Q2PZ37AIC_expCubicRemainder (beta * y) ≤
        Real.exp (-beta * a) *
          ((4 + Real.exp (-(beta * y))) * (beta * y) ^ 4 / 120) :=
      mul_le_mul_of_nonneg_left hr.2 (Real.exp_pos _).le
    _ = (4 * Real.exp (-beta * a) +
        Real.exp (-beta * a) * Real.exp (-(beta * y))) *
          beta ^ 4 * y ^ 4 / 120 := by ring
    _ = (4 * Real.exp (-beta * a) + Real.exp (-beta * (a + y))) *
        beta ^ 4 * y ^ 4 / 120 := by rw [hExp]

/-- The endpoint coefficient never exceeds the AIC maximum coefficient. -/
theorem p4Q2PZ37AID_expCubicRemainder_endpoint_coefficient_le (x : ℝ) :
    (4 + Real.exp (-x)) / 5 ≤ Real.exp (max 0 (-x)) := by
  have hOne : (1 : ℝ) ≤ Real.exp (max 0 (-x)) :=
    Real.one_le_exp (le_max_left _ _)
  have hExp : Real.exp (-x) ≤ Real.exp (max 0 (-x)) :=
    Real.exp_le_exp.mpr (le_max_right _ _)
  linarith only [hOne, hExp]

/-- A normalized chord-weighted quartic has the stated support cap.
The nonnegative branch has weight at most one; the nonpositive branch
has fourth power at most p^4 and exponential at most exp(beta*p). -/
theorem p4Q2PZ37AID_real_chordQuartic_cap_of_support
    (beta p y : ℝ) (hbeta : 0 ≤ beta) (hp : 0 ≤ p)
    (hlo : -p ≤ y) (hhi : y ≤ 3 * p / 2) :
    ((4 + Real.exp (-(beta * y))) / 5) * y ^ 4 ≤
      p ^ 4 * max ((4 + Real.exp (beta * p)) / 5) (81 / 16 : ℝ) := by
  have hpFourth : 0 ≤ p ^ 4 := pow_nonneg hp 4
  have hyFourth : 0 ≤ y ^ 4 := by positivity
  rcases le_total (0 : ℝ) y with hy | hy
  · have hExp : Real.exp (-(beta * y)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hbeta hy))
    have hWeight : (4 + Real.exp (-(beta * y))) / 5 ≤ 1 := by
      linarith only [hExp]
    calc
      ((4 + Real.exp (-(beta * y))) / 5) * y ^ 4 ≤ 1 * y ^ 4 :=
        mul_le_mul_of_nonneg_right hWeight hyFourth
      _ = y ^ 4 := one_mul _
      _ ≤ (3 * p / 2) ^ 4 := pow_le_pow_left₀ hy hhi 4
      _ = p ^ 4 * (81 / 16 : ℝ) := by ring
      _ ≤ p ^ 4 * max ((4 + Real.exp (beta * p)) / 5) (81 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hpFourth
  · have hNeg : 0 ≤ -y := neg_nonneg.mpr hy
    have hNegCap : -y ≤ p := by linarith only [hlo]
    have hFourth : y ^ 4 ≤ p ^ 4 := by
      calc
        y ^ 4 = (-y) ^ 4 := by ring
        _ ≤ p ^ 4 := pow_le_pow_left₀ hNeg hNegCap 4
    have hArg : -(beta * y) ≤ beta * p := by
      calc
        -(beta * y) = beta * (-y) := by ring
        _ ≤ beta * p := mul_le_mul_of_nonneg_left hNegCap hbeta
    have hExp : Real.exp (-(beta * y)) ≤ Real.exp (beta * p) :=
      Real.exp_le_exp.mpr hArg
    have hWeight : (4 + Real.exp (-(beta * y))) / 5 ≤
        (4 + Real.exp (beta * p)) / 5 := by
      linarith only [hExp]
    have hCapNonneg : 0 ≤ (4 + Real.exp (beta * p)) / 5 :=
      div_nonneg (add_nonneg (by norm_num) (Real.exp_nonneg _)) (by norm_num)
    calc
      ((4 + Real.exp (-(beta * y))) / 5) * y ^ 4 ≤
          ((4 + Real.exp (beta * p)) / 5) * y ^ 4 :=
        mul_le_mul_of_nonneg_right hWeight hyFourth
      _ ≤ ((4 + Real.exp (beta * p)) / 5) * p ^ 4 :=
        mul_le_mul_of_nonneg_left hFourth hCapNonneg
      _ = p ^ 4 * ((4 + Real.exp (beta * p)) / 5) := mul_comm _ _
      _ ≤ p ^ 4 * max ((4 + Real.exp (beta * p)) / 5) (81 / 16 : ℝ) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) hpFourth

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AID_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AID_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AID_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AID_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AID_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "X" => p4Q2PZ37AHZ_originalCenteredCrossing H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "Q4" => p4Q2PZ37AHZ_originalSourceFourthHaarMoment H
local notation "D" => p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment H
local notation "Msrc" => p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "fp" => p4Q2PZ37AHY_originalSourcePositivePart H
local notation "fm" => p4Q2PZ37AHY_originalSourceNegativePart H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "aB" => p4Q2PZ37AIC_originalBoundaryConstant H
local notation "Y" => p4Q2PZ37AIC_originalCenteredAction H
local notation "Rc4" => p4Q2PZ37AIC_originalFactoredFourthOrderRemainder H
local notation "Pc3" => p4Q2PZ37AIC_originalFactoredCubicApproximation H
local notation "qWeight" => p4Q2PZ37AIC_originalFactoredRemainderWeight H
local notation "J4wp" => p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment H
local notation "J4wm" => p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment H

local instance p4Q2PZ37AID_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Convex-chord weight made from the exact outer exponential and the
unchanged original complete Boltzmann kernel. -/
def p4Q2PZ37AID_originalChordRemainderWeight
    (beta : ℝ) (A B : Cfg) : ℝ :=
  (4 * Real.exp (-beta * aB B) + K beta A B) / 5

local notation "qChord" => p4Q2PZ37AID_originalChordRemainderWeight H

theorem p4Q2PZ37AID_originalChordRemainderWeight_continuous
    (beta : ℝ) (B : Cfg) :
    Continuous (fun A : Cfg => qChord beta A B) := by
  have hKernel : Continuous (fun A : Cfg => K beta A B) := by
    simpa only
      [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann] using
      (Real.continuous_exp.comp
        (continuous_const.mul (p4Q2PZ37AHP_originalFullAction_continuous H B)) :
        Continuous (fun A : Cfg => Real.exp (-beta * S A B)))
  unfold p4Q2PZ37AID_originalChordRemainderWeight
  exact (continuous_const.add hKernel).div_const 5

theorem p4Q2PZ37AID_originalChordRemainderWeight_pos
    (beta : ℝ) (A B : Cfg) : 0 < qChord beta A B := by
  unfold p4Q2PZ37AID_originalChordRemainderWeight
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
    H 2 beta A B]
  positivity

/-- At nonnegative coupling both exact endpoint exponentials lie below AIC's
maximum weight, so their convex average lies below it too. -/
theorem p4Q2PZ37AID_originalChordRemainderWeight_le_AIC
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    qChord beta A B ≤ qWeight beta A B := by
  have hOuter : Real.exp (-beta * aB B) ≤ qWeight beta A B := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (min_le_left (aB B) (S A B))
      (neg_nonpos.mpr hbeta)
  have hKernel : K beta A B ≤ qWeight beta A B := by
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
      H 2 beta A B]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonpos_left (min_le_right (aB B) (S A B))
      (neg_nonpos.mpr hbeta)
  unfold p4Q2PZ37AID_originalChordRemainderWeight
  linarith only [hOuter, hKernel]

/-- Strict pointwise tightening wherever the centered action is nonzero.
No strict inequality between the integrated moments is inferred here. -/
theorem p4Q2PZ37AID_originalChordRemainderWeight_lt_AIC_of_centeredAction_ne_zero
    (beta : ℝ) (hbeta : 0 < beta) (A B : Cfg) (hY : Y A B ≠ 0) :
    qChord beta A B < qWeight beta A B := by
  have hFull :=
    p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction H A B
  rcases lt_trichotomy (Y A B) 0 with hy | hzero | hy
  · have hOrder : S A B < aB B := by linarith only [hFull, hy]
    have hStrict : Real.exp (-beta * aB B) < K beta A B := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
        H 2 beta A B]
      apply Real.exp_lt_exp.mpr
      exact mul_lt_mul_of_neg_left hOrder (neg_neg_of_pos hbeta)
    have hOld : qWeight beta A B = K beta A B := by
      unfold p4Q2PZ37AIC_originalFactoredRemainderWeight
      rw [min_eq_right hOrder.le,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
          H 2 beta A B]
    unfold p4Q2PZ37AID_originalChordRemainderWeight
    rw [hOld]
    linarith only [hStrict]
  · exact (hY hzero).elim
  · have hOrder : aB B < S A B := by linarith only [hFull, hy]
    have hStrict : K beta A B < Real.exp (-beta * aB B) := by
      rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
        H 2 beta A B]
      apply Real.exp_lt_exp.mpr
      exact mul_lt_mul_of_neg_left hOrder (neg_neg_of_pos hbeta)
    have hOld : qWeight beta A B = Real.exp (-beta * aB B) := by
      unfold p4Q2PZ37AIC_originalFactoredRemainderWeight
      rw [min_eq_left hOrder.le]
    unfold p4Q2PZ37AID_originalChordRemainderWeight
    rw [hOld]
    linarith only [hStrict]

theorem p4Q2PZ37AID_originalChordRemainderWeight_le_rightHalfweight
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    qChord beta A B ≤ Real.exp (-beta * (W B / 2)) :=
  (p4Q2PZ37AID_originalChordRemainderWeight_le_AIC H beta hbeta A B).trans
    (p4Q2PZ37AIC_originalFactoredRemainderWeight_le_rightHalfweight
      H beta hbeta A B)

theorem p4Q2PZ37AID_originalChordRemainderWeight_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    qChord beta A B ≤ 1 :=
  (p4Q2PZ37AID_originalChordRemainderWeight_le_AIC H beta hbeta A B).trans
    (p4Q2PZ37AIC_originalFactoredRemainderWeight_le_one H beta hbeta A B)

/-- Integrability of genuine chord-weighted centered quartic correlations. -/
theorem p4Q2PZ37AID_originalChordWeightedFourth_integrable
    (g : Cfg → ℝ) (hg : Continuous g) (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => g A * qChord beta A B * (Y A B) ^ 4) muH :=
  ((hg.mul (p4Q2PZ37AID_originalChordRemainderWeight_continuous H beta B)).mul
    ((p4Q2PZ37AIC_originalCenteredAction_continuous H B).pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- True original positive-source / original-kernel mixture / centered-quartic integral. -/
def p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fp A * qChord beta A B * (Y A B) ^ 4 ∂muH

/-- True original negative-source counterpart, kept as a separate correlation. -/
def p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fm A * qChord beta A B * (Y A B) ^ 4 ∂muH

local notation "J4cp" => p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment H
local notation "J4cm" => p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment H

theorem p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_nonneg
    (beta : ℝ) (B : Cfg) :
    0 ≤ J4cp beta B ∧ 0 ≤ J4cm beta B := by
  have hWeight (A : Cfg) : 0 ≤ qChord beta A B :=
    (p4Q2PZ37AID_originalChordRemainderWeight_pos H beta A B).le
  have hFourth (A : Cfg) : 0 ≤ (Y A B) ^ 4 := by positivity
  constructor
  · exact integral_nonneg (fun A =>
      mul_nonneg
        (mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1 (hWeight A))
        (hFourth A))
  · exact integral_nonneg (fun A =>
      mul_nonneg
        (mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).2 (hWeight A))
        (hFourth A))

/-- Each new correlated moment is bounded by its own AIC counterpart. -/
theorem p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_le_AIC
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    J4cp beta B ≤ J4wp beta B ∧ J4cm beta B ≤ J4wm beta B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hFourth (A : Cfg) : 0 ≤ (Y A B) ^ 4 := by positivity
  constructor
  · unfold p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment
      p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment
    apply integral_mono
      (p4Q2PZ37AID_originalChordWeightedFourth_integrable H fp hp beta B)
      (p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable H fp hp beta B)
    intro A
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (p4Q2PZ37AID_originalChordRemainderWeight_le_AIC H beta hbeta A B)
        (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1)
      (hFourth A)
  · unfold p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment
      p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment
    apply integral_mono
      (p4Q2PZ37AID_originalChordWeightedFourth_integrable H fm hm beta B)
      (p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable H fm hm beta B)
    intro A
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (p4Q2PZ37AID_originalChordRemainderWeight_le_AIC H beta hbeta A B)
        (p4Q2PZ37AHY_originalSourceParts_nonneg H A).2)
      (hFourth A)

/-- The SAME actual AIC centered kernel error has the improved chord bound.
This interval holds at every real coupling, including negative beta and beta=0. -/
theorem p4Q2PZ37AID_originalFactoredKernelRemainder_chordInterval
    (beta : ℝ) (A B : Cfg) :
    0 ≤ Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ∧
      Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ≤
          qChord beta A B * beta ^ 4 * (Y A B) ^ 4 / 24 := by
  have h := p4Q2PZ37AID_expCubicRemainder_factoredChordInterval
    beta (aB B) (Y A B)
  rw [← p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction
    H A B,
    ← periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
      H 2 beta A B] at h
  refine ⟨h.1, ?_⟩
  calc
    Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ≤
        (4 * Real.exp (-beta * aB B) + K beta A B) *
          beta ^ 4 * (Y A B) ^ 4 / 120 := h.2
    _ = qChord beta A B * beta ^ 4 * (Y A B) ^ 4 / 24 := by
      unfold p4Q2PZ37AID_originalChordRemainderWeight
      ring

/-- Negative source part below, positive source part above: both bounds retain
the actual centered quartic correlation and pointwise exponential weight. -/
theorem p4Q2PZ37AID_originalFactoredFourthOrderRemainder_chordInterval
    (beta : ℝ) (B : Cfg) :
    -((beta ^ 4 / 24) * J4cm beta B) ≤ Rc4 beta B ∧
      Rc4 beta B ≤ (beta ^ 4 / 24) * J4cp beta B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hpInt := p4Q2PZ37AID_originalChordWeightedFourth_integrable H fp hp beta B
  have hmInt := p4Q2PZ37AID_originalChordWeightedFourth_integrable H fm hm beta B
  have hrInt := p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_integrable H beta B
  have hPoint (A : Cfg) := p4Q2PZ37AIA_real_signedNonnegativeError_interval
    (fCont A)
    (Real.exp (-beta * aB B) * p4Q2PZ37AIC_expCubicRemainder (beta * Y A B))
    (qChord beta A B * beta ^ 4 * (Y A B) ^ 4 / 24)
    (p4Q2PZ37AID_originalFactoredKernelRemainder_chordInterval H beta A B)
  constructor
  · calc
      -((beta ^ 4 / 24) * J4cm beta B) =
          ∫ A : Cfg, -(beta ^ 4 / 24) *
            (fm A * qChord beta A B * (Y A B) ^ 4) ∂muH := by
        rw [integral_const_mul]
        unfold p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment
        ring
      _ ≤ Rc4 beta B := by
        unfold p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
        apply integral_mono (hmInt.const_mul _) hrInt
        intro A
        calc
          -(beta ^ 4 / 24) * (fm A * qChord beta A B * (Y A B) ^ 4) =
              -((|fCont A| - fCont A) / 2) *
                (qChord beta A B * beta ^ 4 * (Y A B) ^ 4 / 24) := by
            unfold p4Q2PZ37AHY_originalSourceNegativePart
            ring
          _ ≤ fCont A *
              (Real.exp (-beta * aB B) *
                p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) := (hPoint A).1
  · calc
      Rc4 beta B ≤
          ∫ A : Cfg, (beta ^ 4 / 24) *
            (fp A * qChord beta A B * (Y A B) ^ 4) ∂muH := by
        unfold p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
        apply integral_mono hrInt (hpInt.const_mul _)
        intro A
        calc
          fCont A *
              (Real.exp (-beta * aB B) *
                p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) ≤
              ((|fCont A| + fCont A) / 2) *
                (qChord beta A B * beta ^ 4 * (Y A B) ^ 4 / 24) := (hPoint A).2
          _ = (beta ^ 4 / 24) * (fp A * qChord beta A B * (Y A B) ^ 4) := by
            unfold p4Q2PZ37AHY_originalSourcePositivePart
            ring
      _ = (beta ^ 4 / 24) * J4cp beta B := integral_const_mul _ _

/-- Exact interval for the SAME physical transfer and SAME AIC cubic center,
now valid for every real beta with the actual-kernel chord correlations. -/
theorem p4Q2PZ37AID_originalTransfer_chordQuarticInterval
    (beta : ℝ) (B : Cfg) :
    Pc3 beta B - (beta ^ 4 / 24) * J4cm beta B ≤ T beta f0 B ∧
      T beta f0 B ≤ Pc3 beta B + (beta ^ 4 / 24) * J4cp beta B := by
  have hr := p4Q2PZ37AID_originalFactoredFourthOrderRemainder_chordInterval H beta B
  rw [p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub H beta B] at hr
  constructor <;> linarith only [hr.1, hr.2]

/-- Genuine interval containment at nonnegative coupling. The old and new
intervals have exactly the same actual transfer, center and remainder. -/
theorem p4Q2PZ37AID_originalChordTransferInterval_subset_AIC
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Set.Icc
      (Pc3 beta B - (beta ^ 4 / 24) * J4cm beta B)
      (Pc3 beta B + (beta ^ 4 / 24) * J4cp beta B) ⊆
    Set.Icc
      (Pc3 beta B - (beta ^ 4 / 24) * J4wm beta B)
      (Pc3 beta B + (beta ^ 4 / 24) * J4wp beta B) := by
  have hMom := p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_le_AIC
    H beta hbeta B
  have hCoeff : 0 ≤ beta ^ 4 / 24 := by positivity
  have hp := mul_le_mul_of_nonneg_left hMom.1 hCoeff
  have hm := mul_le_mul_of_nonneg_left hMom.2 hCoeff
  intro z hz
  constructor <;> linarith only [hp, hm, hz.1, hz.2]

/-- Full chord margin for the original physical transfer. The all-real
remainder interval makes an additional beta sign hypothesis unnecessary. -/
theorem p4Q2PZ37AID_originalTransfer_negative_of_chordQuarticMargin
    (beta : ℝ) (B : Cfg)
    (hmargin : (beta ^ 4 / 24) * J4cp beta B <
      Real.exp (-beta * aB B) *
        (beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B))) :
    T beta f0 B < 0 := by
  have hu := (p4Q2PZ37AID_originalTransfer_chordQuarticInterval H beta B).2
  unfold p4Q2PZ37AIC_originalFactoredCubicApproximation at hu
  linarith only [hu, hmargin]

/-- A stronger variance-only sufficient condition at nonnegative coupling. -/
theorem p4Q2PZ37AID_originalTransfer_negative_of_chordVarianceMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hmargin : (beta ^ 4 / 24) * J4cp beta B <
      Real.exp (-beta * aB B) * (beta * Vsrc)) :
    T beta f0 B < 0 := by
  have hu := (p4Q2PZ37AID_originalTransfer_chordQuarticInterval H beta B).2
  have hc := p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance
    H beta hbeta B
  linarith only [hu, hc, hmargin]

/-- Every existing AIC full weighted certificate remains a chord certificate. -/
theorem p4Q2PZ37AID_originalAICQuarticMargin_implies_chordMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hmargin : (beta ^ 4 / 24) * J4wp beta B <
      Real.exp (-beta * aB B) *
        (beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B))) :
    (beta ^ 4 / 24) * J4cp beta B <
      Real.exp (-beta * aB B) *
        (beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B)) :=
  (mul_le_mul_of_nonneg_left
    (p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_le_AIC
      H beta hbeta B).1 (by positivity)).trans_lt hmargin

/-- Unconditional chord interval at the unchanged original positive coupling. -/
theorem p4Q2PZ37AID_originalFixedTransfer_chordQuarticInterval (B : Cfg) :
    Pc3 beta0 B - (beta0 ^ 4 / 24) * J4cm beta0 B ≤ T beta0 f0 B ∧
      T beta0 f0 B ≤ Pc3 beta0 B + (beta0 ^ 4 / 24) * J4cp beta0 B :=
  p4Q2PZ37AID_originalTransfer_chordQuarticInterval H beta0 B

/-- Actual fixed-coupling negativity still requires its genuine chord margin. -/
theorem p4Q2PZ37AID_originalFixedTransfer_negative_of_chordQuarticMargin
    (B : Cfg)
    (hmargin : (beta0 ^ 4 / 24) * J4cp beta0 B <
      Real.exp (-beta0 * aB B) *
        (beta0 * Vsrc + (beta0 ^ 3 / 6) * (Q4 + 3 * D B))) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AID_originalTransfer_negative_of_chordQuarticMargin H beta0 B hmargin

/-- Genuine normalized convex-chord weight after the exact AIC factorization. -/
def p4Q2PZ37AID_originalNormalizedChordRemainderWeight
    (beta : ℝ) (A B : Cfg) : ℝ :=
  (4 + Real.exp (-(beta * Y A B))) / 5

local notation "nChord" => p4Q2PZ37AID_originalNormalizedChordRemainderWeight H

theorem p4Q2PZ37AID_originalNormalizedChordRemainderWeight_continuous
    (beta : ℝ) (B : Cfg) :
    Continuous (fun A : Cfg => nChord beta A B) :=
  (continuous_const.add
    (p4Q2PZ37AIC_originalCenteredKernel_continuous H beta B)).div_const 5

theorem p4Q2PZ37AID_originalNormalizedChordRemainderWeight_nonneg
    (beta : ℝ) (A B : Cfg) : 0 ≤ nChord beta A B := by
  unfold p4Q2PZ37AID_originalNormalizedChordRemainderWeight
  positivity

/-- The actual kernel in the chord weight factors exactly, with no beta restriction. -/
theorem p4Q2PZ37AID_originalChordRemainderWeight_eq_const_mul_normalized
    (beta : ℝ) (A B : Cfg) :
    qChord beta A B = Real.exp (-beta * aB B) * nChord beta A B := by
  unfold p4Q2PZ37AID_originalChordRemainderWeight
    p4Q2PZ37AID_originalNormalizedChordRemainderWeight
  rw [p4Q2PZ37AIC_originalKernel_factorization H beta A B]
  ring

/-- Continuous original weights give genuine normalized quartic integrability. -/
theorem p4Q2PZ37AID_originalNormalizedChordWeightedFourth_integrable
    (g : Cfg → ℝ) (hg : Continuous g) (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => g A * nChord beta A B * (Y A B) ^ 4) muH :=
  ((hg.mul
    (p4Q2PZ37AID_originalNormalizedChordRemainderWeight_continuous H beta B)).mul
    ((p4Q2PZ37AIC_originalCenteredAction_continuous H B).pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Actual positive-source normalized chord/quartic correlation. -/
def p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fp A * nChord beta A B * (Y A B) ^ 4 ∂muH

local notation "N4cp" => p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment H

theorem p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_nonneg
    (beta : ℝ) (B : Cfg) : 0 ≤ N4cp beta B := by
  apply integral_nonneg
  intro A
  exact mul_nonneg
    (mul_nonneg (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1
      (p4Q2PZ37AID_originalNormalizedChordRemainderWeight_nonneg H beta A B))
    (by positivity)

/-- Exact relation of the two genuine Haar integrals; no independence is used. -/
theorem p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment_eq_normalized
    (beta : ℝ) (B : Cfg) :
    J4cp beta B = Real.exp (-beta * aB B) * N4cp beta B := by
  unfold p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment
    p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment
  calc
    (∫ A : Cfg, fp A * qChord beta A B * (Y A B) ^ 4 ∂muH) =
        ∫ A : Cfg, Real.exp (-beta * aB B) *
          (fp A * nChord beta A B * (Y A B) ^ 4) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AID_originalChordRemainderWeight_eq_const_mul_normalized H beta A B]
      ring
    _ = Real.exp (-beta * aB B) *
        (∫ A : Cfg, fp A * nChord beta A B * (Y A B) ^ 4 ∂muH) := by
      rw [integral_const_mul]

/-- The common strictly positive factor cancels for every real beta and signal.
The pinned mathlib right₀ lemma cancels a common factor on the LEFT. -/
theorem p4Q2PZ37AID_originalPositiveChordQuarticMargin_iff_normalized
    (beta signal : ℝ) (B : Cfg) :
    (beta ^ 4 / 24) * J4cp beta B <
        Real.exp (-beta * aB B) * signal ↔
      (beta ^ 4 / 24) * N4cp beta B < signal := by
  rw [p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment_eq_normalized
    H beta B]
  rw [show (beta ^ 4 / 24) * (Real.exp (-beta * aB B) * N4cp beta B) =
      Real.exp (-beta * aB B) * ((beta ^ 4 / 24) * N4cp beta B) by ring]
  exact mul_lt_mul_iff_right₀ (Real.exp_pos _)

/-- Full true cubic signal with its retained fourth and mixed source moments. -/
theorem p4Q2PZ37AID_originalChordQuarticMargin_iff_normalized
    (beta : ℝ) (B : Cfg) :
    (beta ^ 4 / 24) * J4cp beta B <
        Real.exp (-beta * aB B) *
          (beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B)) ↔
      (beta ^ 4 / 24) * N4cp beta B <
        beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B) :=
  p4Q2PZ37AID_originalPositiveChordQuarticMargin_iff_normalized H beta
    (beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B)) B

/-- A genuine normalized margin implies the original physical conclusion.
The scalar chord remainder and this root-provided theorem are all-real-beta. -/
theorem p4Q2PZ37AID_originalTransfer_negative_of_normalizedChordQuarticMargin
    (beta : ℝ) (B : Cfg)
    (hmargin : (beta ^ 4 / 24) * N4cp beta B <
      beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B)) :
    T beta f0 B < 0 :=
  p4Q2PZ37AID_originalTransfer_negative_of_chordQuarticMargin H beta B
    ((p4Q2PZ37AID_originalChordQuarticMargin_iff_normalized H beta B).mpr hmargin)

/-- A pointwise cap is needed only where the original source is nonnegative.
The complementary region contributes zero because fp vanishes there.
Only the established UNWEIGHTED positive half-mass is used. -/
theorem p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_of_support_cap
    (beta c : ℝ) (B : Cfg)
    (hCap : ∀ A : Cfg, 0 ≤ fCont A →
      nChord beta A B * (Y A B) ^ 4 ≤ c) :
    N4cp beta B ≤ c * Msrc / 2 := by
  have hp := (p4Q2PZ37AHY_originalSourceParts_continuous H).1
  have hInt := p4Q2PZ37AID_originalNormalizedChordWeightedFourth_integrable H
    (p4Q2PZ37AHY_originalSourcePositivePart H) hp beta B
  have hpInt : Integrable (fun A : Cfg => fp A * c) muH :=
    (hp.mul continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPoint (A : Cfg) :
      fp A * nChord beta A B * (Y A B) ^ 4 ≤ fp A * c := by
    by_cases hf : 0 ≤ fCont A
    · calc
        fp A * nChord beta A B * (Y A B) ^ 4 =
            fp A * (nChord beta A B * (Y A B) ^ 4) := by ring
        _ ≤ fp A * c :=
          mul_le_mul_of_nonneg_left (hCap A hf)
            (p4Q2PZ37AHY_originalSourceParts_nonneg H A).1
    · have hf' : fCont A ≤ 0 := le_of_lt (lt_of_not_ge hf)
      have hfp : fp A = 0 := by
        change (|fCont A| + fCont A) / 2 = 0
        rw [abs_of_nonpos hf']
        ring
      simp only [hfp, zero_mul, le_refl]
  calc
    N4cp beta B ≤ (∫ A : Cfg, fp A * c ∂muH) :=
      integral_mono hInt hpInt hPoint
    _ = c * Msrc / 2 := by
      rw [integral_mul_const, (p4Q2PZ37AHY_originalSourceParts_HaarMass H).1]
      ring

/-- On the nonnegative-source support the centered action has the improved
lower endpoint -p. This statement is not applied to the negative source part. -/
theorem p4Q2PZ37AID_originalPositiveSource_centeredAction_interval
    (A B : Cfg) (hf : 0 ≤ fCont A) :
    -pH ≤ Y A B ∧ Y A B ≤ 3 * pH / 2 := by
  have hSource := (abs_le.mp
    (p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A)).2
  have hCross : -pH ≤ X A B ∧ X A B ≤ pH :=
    abs_le.mp (show |X A B| ≤ pH from
      p4Q2PZ37AHQ_originalCrossing_centered_abs_le_count H A B)
  unfold p4Q2PZ37AIC_originalCenteredAction
  constructor <;> linarith only [hf, hSource, hCross.1, hCross.2]

/-- One-sided genuine normalized quartic bound using the source support and
the original UNWEIGHTED positive half-mass. No factor independence is used. -/
theorem p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_supportBudget
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    N4cp beta B ≤
      (pH ^ 4 * max ((4 + Real.exp (beta * pH)) / 5) (81 / 16 : ℝ)) * Msrc / 2 := by
  apply p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_of_support_cap
    H beta
    (pH ^ 4 * max ((4 + Real.exp (beta * pH)) / 5) (81 / 16 : ℝ)) B
  intro A hf
  have hY := p4Q2PZ37AID_originalPositiveSource_centeredAction_interval H A B hf
  exact p4Q2PZ37AID_real_chordQuartic_cap_of_support
    beta pH (Y A B) hbeta (p4Q2PZ37AHN_count_pos H).le hY.1 hY.2

/-- Normalized UPPER error budget, from the positive-source support only.
It is not a symmetric or absolute-value bound for the signed remainder. -/
def p4Q2PZ37AID_originalPositiveChordQuarticBudget (beta : ℝ) : ℝ :=
  beta ^ 4 * Msrc * pH ^ 4 *
    max ((4 + Real.exp (beta * pH)) / 5) (81 / 16 : ℝ) / 48

local notation "EChord" => p4Q2PZ37AID_originalPositiveChordQuarticBudget H

theorem p4Q2PZ37AID_originalPositiveChordQuarticBudget_dominates_normalized
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    (beta ^ 4 / 24) * N4cp beta B ≤ EChord beta := by
  calc
    (beta ^ 4 / 24) * N4cp beta B ≤
        (beta ^ 4 / 24) *
          ((pH ^ 4 * max ((4 + Real.exp (beta * pH)) / 5) (81 / 16 : ℝ)) *
            Msrc / 2) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_supportBudget
          H beta hbeta B) (by positivity)
    _ = EChord beta := by
      unfold p4Q2PZ37AID_originalPositiveChordQuarticBudget
      ring

/-- Upper bound on the ORIGINAL physical transfer with the exact exponential
still multiplying both the genuine cubic signal and the one-sided budget. -/
theorem p4Q2PZ37AID_originalTransfer_le_chordSupportBudget
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    T beta f0 B ≤ Real.exp (-beta * aB B) *
      (-(beta * Vsrc) - (beta ^ 3 / 6) * (Q4 + 3 * D B) + EChord beta) := by
  have hu := (p4Q2PZ37AID_originalTransfer_chordQuarticInterval H beta B).2
  have he := p4Q2PZ37AID_originalPositiveChordQuarticBudget_dominates_normalized
    H beta hbeta B
  calc
    T beta f0 B ≤ Pc3 beta B + (beta ^ 4 / 24) * J4cp beta B := hu
    _ = Real.exp (-beta * aB B) *
        (-(beta * Vsrc) - (beta ^ 3 / 6) * (Q4 + 3 * D B) +
          (beta ^ 4 / 24) * N4cp beta B) := by
      rw [p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment_eq_normalized
        H beta B]
      unfold p4Q2PZ37AIC_originalFactoredCubicApproximation
      ring
    _ ≤ Real.exp (-beta * aB B) *
        (-(beta * Vsrc) - (beta ^ 3 / 6) * (Q4 + 3 * D B) + EChord beta) :=
      mul_le_mul_of_nonneg_left (add_le_add_right he _) (Real.exp_pos _).le

/-- A support-budget certificate is a stronger sufficient condition than the
true normalized chord margin. Its satisfaction is not assumed as a theorem. -/
theorem p4Q2PZ37AID_originalTransfer_negative_of_chordSupportBudget
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hmargin : EChord beta <
      beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B)) :
    T beta f0 B < 0 :=
  p4Q2PZ37AID_originalTransfer_negative_of_normalizedChordQuarticMargin H beta B
    ((p4Q2PZ37AID_originalPositiveChordQuarticBudget_dominates_normalized
      H beta hbeta B).trans_lt hmargin)

/-- The original fixed coupling is retained, with its support-budget margin
explicitly present. No witness or physical spectral gap is asserted. -/
theorem p4Q2PZ37AID_originalFixedTransfer_negative_of_chordSupportBudget
    (B : Cfg)
    (hmargin : EChord beta0 <
      beta0 * Vsrc + (beta0 ^ 3 / 6) * (Q4 + 3 * D B)) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AID_originalTransfer_negative_of_chordSupportBudget H beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le B hmargin

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AID_expCubicRemainder_chordUpper
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AID_expCubicRemainder_chordInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AID_expCubicRemainder_factoredChordInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AID_expCubicRemainder_endpoint_coefficient_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AID_real_chordQuartic_cap_of_support
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_le_AIC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_lt_AIC_of_centeredAction_ne_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_le_rightHalfweight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordWeightedFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalNegativeChordWeightedCenteredFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordWeightedCenteredFourthMoments_le_AIC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalFactoredKernelRemainder_chordInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalFactoredFourthOrderRemainder_chordInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalTransfer_chordQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordTransferInterval_subset_AIC
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalTransfer_negative_of_chordQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalTransfer_negative_of_chordVarianceMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalAICQuarticMargin_implies_chordMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalFixedTransfer_chordQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalFixedTransfer_negative_of_chordQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalNormalizedChordRemainderWeight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalNormalizedChordRemainderWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalNormalizedChordRemainderWeight_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordRemainderWeight_eq_const_mul_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalNormalizedChordWeightedFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveChordWeightedCenteredFourthMoment_eq_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveChordQuarticMargin_iff_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalChordQuarticMargin_iff_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalTransfer_negative_of_normalizedChordQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_of_support_cap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveSource_centeredAction_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveNormalizedChordFourthMoment_le_supportBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveChordQuarticBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalPositiveChordQuarticBudget_dominates_normalized
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalTransfer_le_chordSupportBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalTransfer_negative_of_chordSupportBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AID_originalFixedTransfer_negative_of_chordSupportBudget
