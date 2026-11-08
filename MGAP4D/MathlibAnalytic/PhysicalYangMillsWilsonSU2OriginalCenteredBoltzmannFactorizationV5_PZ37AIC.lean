import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuarticBudgetObstructionV5_PZ37AIB
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIC — original centered Boltzmann factorization and weighted remainder

Keep the original complete one-slab Wilson action, BOTH spatial halfweights,
signed ZW source, physical L2 transfer and genuine spatial product Haar.
With X=Cross-p_H, a(B)=(3*p_H+W(B))/2 and Y=f+X, the original action is
S=a+Y. Extract exp(-beta*a) exactly; the source-weighted centered moments
are integral f*Y=V, integral f*Y^2=0, integral f*Y^3=Q4+3*D(B).
The even mixed cancellation uses AHS's Ward theorem, not odd symmetry alone.

The genuine cubic exponential remainder r4(x) is nonnegative for ALL real x
and at most exp(max(0,-x))*x^4/24. Its negative-argument proof discounts the
positive exponential and compares derivatives, preserving the factor 1/24.
There is no smallness assumption, and Y is never assumed nonnegative.

The actual factored error satisfies T=Pc3+Rc4 for every real beta, where
Pc3=exp(-beta*a)*[-beta*V-(beta^3/6)*(Q4+3*D)].
At beta>=0 the exact outer factor yields the retained pointwise weight
qWeight=exp(-beta*min(a,S)), rather than an independent-moment assumption.
True positive/negative-source weighted centered quartic integrals give
-(beta^4/24)*J4wm <= Rc4 <= (beta^4/24)*J4wp.
The physical transfer inherits this interval and explicit conditional
negative-sign margins, including at the unchanged original fixed beta0.

Pc3 is strictly negative for beta>0. No actual fixed-beta sign witness,
positive/negative shells, volume-uniform coercivity, Hamiltonian gap or
continuum Yang-Mills mass gap is claimed. AIB's old coarse-budget obstruction
is preserved. All prior definitions, proof histories, roots, pins and
workflows remain unchanged; this is one appended Lean leaf.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The genuine cubic Taylor remainder of the negative exponential. -/
def p4Q2PZ37AIC_expCubicRemainder (x : ℝ) : ℝ :=
  Real.exp (-x) - (1 - x + x ^ 2 / 2 - x ^ 3 / 6)

theorem p4Q2PZ37AIC_expCubicRemainder_continuous :
    Continuous p4Q2PZ37AIC_expCubicRemainder := by
  unfold p4Q2PZ37AIC_expCubicRemainder
  fun_prop

/-- Discounting the positive exponential leaves a function with derivative
exp(-t)*t^3/6, between zero and t^3/6 for t >= 0. -/
theorem p4Q2PZ37AIC_exp_pos_discountedCubicRemainder_interval
    (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) ∧
      1 - Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) ≤ x ^ 4 / 24 := by
  have hDeriv (t : ℝ) :
      HasDerivAt
        (fun y : ℝ => 1 - Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6))
        (Real.exp (-t) * t ^ 3 / 6) t := by
    convert (hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).neg.exp).mul
        ((((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).add
          (((hasDerivAt_id t).pow 2).div_const (2 : ℝ))).add
            (((hasDerivAt_id t).pow 3).div_const (6 : ℝ)))) using 1
    simp
    ring
  have hPoly (t : ℝ) :
      HasDerivAt (fun y : ℝ => y ^ 4 / 24) (t ^ 3 / 6) t := by
    convert ((hasDerivAt_id t).pow 4).div_const (24 : ℝ) using 1
    simp
    ring
  have hCont : Continuous
      (fun y : ℝ => 1 - Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6)) := by
    fun_prop
  have hLower :
      0 ≤ 1 - Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (f := fun _ : ℝ => (0 : ℝ)) (f' := fun _ : ℝ => (0 : ℝ))
      (a := (0 : ℝ)) (b := x)
      (B := fun y : ℝ => 1 - Real.exp (-y) * (1 + y + y ^ 2 / 2 + y ^ 3 / 6))
      (B' := fun y : ℝ => Real.exp (-y) * y ^ 3 / 6)
      (by fun_prop)
      (fun t _ => (hasDerivAt_const t (0 : ℝ)).hasDerivWithinAt)
      (by norm_num)
      hCont.continuousOn
      (fun t _ => (hDeriv t).hasDerivWithinAt)
      (fun t ht => ?_)
      ⟨hx, le_rfl⟩
    exact div_nonneg
      (mul_nonneg (Real.exp_pos (-t)).le (pow_nonneg ht.1 3)) (by norm_num)
  have hUpper :
      1 - Real.exp (-x) * (1 + x + x ^ 2 / 2 + x ^ 3 / 6) ≤ x ^ 4 / 24 := by
    apply image_le_of_deriv_right_le_deriv_boundary
      (a := (0 : ℝ)) (b := x)
      (B := fun y : ℝ => y ^ 4 / 24) (B' := fun y : ℝ => y ^ 3 / 6)
      hCont.continuousOn
      (fun t _ => (hDeriv t).hasDerivWithinAt)
      (by norm_num)
      (by fun_prop)
      (fun t _ => (hPoly t).hasDerivWithinAt)
      (fun t ht => ?_)
      ⟨hx, le_rfl⟩
    have hExp : Real.exp (-t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.1)
    simpa only [one_mul] using
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hExp (pow_nonneg ht.1 3))
        (by norm_num : (0 : ℝ) ≤ 6))
  exact ⟨hLower, hUpper⟩

/-- The exact quartic remainder bound at every real argument. On the
nonnegative half-line the exponential coefficient is exactly one. -/
theorem p4Q2PZ37AIC_expCubicRemainder_interval (x : ℝ) :
    0 ≤ p4Q2PZ37AIC_expCubicRemainder x ∧
      p4Q2PZ37AIC_expCubicRemainder x ≤
        Real.exp (max 0 (-x)) * x ^ 4 / 24 := by
  rcases le_total (0 : ℝ) x with hx | hx
  · simpa only [p4Q2PZ37AIC_expCubicRemainder,
      max_eq_left (neg_nonpos.mpr hx), Real.exp_zero, one_mul] using
        p4Q2PZ37AIA_exp_neg_quarticRemainder x hx
  · have hNeg : 0 ≤ -x := neg_nonneg.mpr hx
    have h := p4Q2PZ37AIC_exp_pos_discountedCubicRemainder_interval (-x) hNeg
    have hCancel : Real.exp (-x) * Real.exp (-(-x)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hIdentity :
        p4Q2PZ37AIC_expCubicRemainder x =
          Real.exp (-x) *
            (1 - Real.exp (-(-x)) * (1 + (-x) + (-x) ^ 2 / 2 + (-x) ^ 3 / 6)) := by
      unfold p4Q2PZ37AIC_expCubicRemainder
      rw [mul_sub, mul_one, ← mul_assoc, hCancel, one_mul]
      ring
    constructor
    · rw [hIdentity]
      exact mul_nonneg (Real.exp_pos (-x)).le h.1
    · calc
        p4Q2PZ37AIC_expCubicRemainder x =
            Real.exp (-x) *
              (1 - Real.exp (-(-x)) * (1 + (-x) + (-x) ^ 2 / 2 + (-x) ^ 3 / 6)) :=
          hIdentity
        _ ≤ Real.exp (-x) * ((-x) ^ 4 / 24) :=
          mul_le_mul_of_nonneg_left h.2 (Real.exp_pos (-x)).le
        _ = Real.exp (max 0 (-x)) * x ^ 4 / 24 := by
          rw [max_eq_right hNeg]
          ring

/-- The exact outer exponential retains a pointwise minimum-action weight.
Only the coupling is nonnegative; a and y are arbitrary real numbers. -/
theorem p4Q2PZ37AIC_expCubicRemainder_factored_interval
    (beta a y : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ Real.exp (-beta * a) * p4Q2PZ37AIC_expCubicRemainder (beta * y) ∧
      Real.exp (-beta * a) * p4Q2PZ37AIC_expCubicRemainder (beta * y) ≤
        Real.exp (-beta * min a (a + y)) * beta ^ 4 * y ^ 4 / 24 := by
  have hr := p4Q2PZ37AIC_expCubicRemainder_interval (beta * y)
  have hExp :
      Real.exp (-beta * a) * Real.exp (max 0 (-(beta * y))) =
        Real.exp (-beta * min a (a + y)) := by
    rw [← Real.exp_add]
    congr 1
    by_cases hy : 0 ≤ y
    · have hMax : -(beta * y) ≤ 0 := neg_nonpos.mpr (mul_nonneg hbeta hy)
      have hMin : a ≤ a + y := by linarith only [hy]
      simp only [max_eq_left hMax, min_eq_left hMin, add_zero]
    · have hy' : y ≤ 0 := le_of_lt (lt_of_not_ge hy)
      have hMax : 0 ≤ -(beta * y) :=
        neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hbeta hy')
      have hMin : a + y ≤ a := by linarith only [hy']
      rw [max_eq_right hMax, min_eq_right hMin]
      ring
  refine ⟨mul_nonneg (Real.exp_nonneg _) hr.1, ?_⟩
  calc
    Real.exp (-beta * a) * p4Q2PZ37AIC_expCubicRemainder (beta * y) ≤
        Real.exp (-beta * a) *
          (Real.exp (max 0 (-(beta * y))) * (beta * y) ^ 4 / 24) :=
      mul_le_mul_of_nonneg_left hr.2 (Real.exp_nonneg _)
    _ = (Real.exp (-beta * a) * Real.exp (max 0 (-(beta * y)))) *
        beta ^ 4 * y ^ 4 / 24 := by ring
    _ = Real.exp (-beta * min a (a + y)) * beta ^ 4 * y ^ 4 / 24 := by
      rw [hExp]

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIC_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIC_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIC_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIC_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIC_borel : BorelSpace G :=
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

local instance p4Q2PZ37AIC_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The actual A-independent part of the original full one-slab action. -/
def p4Q2PZ37AIC_originalBoundaryConstant (B : Cfg) : ℝ :=
  (3 * pH + W B) / 2

/-- The original source plus original centered crossing; it may be signed. -/
def p4Q2PZ37AIC_originalCenteredAction (A B : Cfg) : ℝ :=
  fCont A + X A B

local notation "aB" => p4Q2PZ37AIC_originalBoundaryConstant H
local notation "Y" => p4Q2PZ37AIC_originalCenteredAction H

theorem p4Q2PZ37AIC_originalCenteredAction_continuous (B : Cfg) :
    Continuous (fun A : Cfg => Y A B) :=
  (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.add
    (p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B)

/-- A bound on the actual centered fluctuation, with both old bounds retained. -/
theorem p4Q2PZ37AIC_originalCenteredAction_abs_le_threeHalfCount
    (A B : Cfg) :
    |Y A B| ≤ 3 * pH / 2 := by
  have hf := p4Q2PZ37AGN_originalContinuousSource_abs_le_halfCount H A
  have hx : |X A B| ≤ pH :=
    p4Q2PZ37AHQ_originalCrossing_centered_abs_le_count H A B
  calc
    |Y A B| = |fCont A + X A B| := rfl
    _ ≤ |fCont A| + |X A B| := abs_add_le _ _
    _ ≤ pH / 2 + pH := add_le_add hf hx
    _ = 3 * pH / 2 := by ring

theorem p4Q2PZ37AIC_originalBoundaryConstant_nonneg (B : Cfg) :
    0 ≤ aB B := by
  have hp := (p4Q2PZ37AHN_count_pos H).le
  have hw :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) B
  unfold p4Q2PZ37AIC_originalBoundaryConstant
  positivity

/-- Exact re-association of AHZ, keeping BOTH original spatial halfweights. -/
theorem p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction
    (A B : Cfg) :
    S A B = aB B + Y A B := by
  rw [p4Q2PZ37AHZ_originalFullAction_centered_decomposition H A B]
  unfold p4Q2PZ37AIC_originalBoundaryConstant p4Q2PZ37AIC_originalCenteredAction
  ring

/-- The right Wilson halfweight is a floor for BOTH entries of the min weight. -/
theorem p4Q2PZ37AIC_originalMinAction_ge_rightHalfweight
    (A B : Cfg) :
    W B / 2 ≤ min (aB B) (S A B) := by
  have hp := (p4Q2PZ37AHN_count_pos H).le
  have hw :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) A
  have hc := p4Q2PZ37AHQ_originalCrossing_nonneg H A B
  apply le_min
  · unfold p4Q2PZ37AIC_originalBoundaryConstant
    linarith only [hp]
  · unfold periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
    linarith only [hw, hc]

/-- Literal original kernel factorization, for every real coupling. -/
theorem p4Q2PZ37AIC_originalKernel_factorization
    (beta : ℝ) (A B : Cfg) :
    K beta A B =
      Real.exp (-beta * aB B) * Real.exp (-(beta * Y A B)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann
    H 2 beta A B,
    p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction H A B]
  rw [show -beta * (aB B + Y A B) =
    -beta * aB B + -(beta * Y A B) by ring, Real.exp_add]

theorem p4Q2PZ37AIC_originalCenteredKernel_continuous
    (beta : ℝ) (B : Cfg) :
    Continuous (fun A : Cfg => Real.exp (-(beta * Y A B))) :=
  Real.continuous_exp.comp
    ((continuous_const.mul
      (p4Q2PZ37AIC_originalCenteredAction_continuous H B)).neg)

theorem p4Q2PZ37AIC_originalCenteredKernelWeightedSource_integrable
    (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => fCont A * Real.exp (-(beta * Y A B))) muH :=
  ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.mul
    (p4Q2PZ37AIC_originalCenteredKernel_continuous H beta B)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Same physical L2 transfer and same product Haar after exact factor extraction. -/
theorem p4Q2PZ37AIC_originalTransfer_factorization
    (beta : ℝ) (B : Cfg) :
    T beta f0 B = Real.exp (-beta * aB B) *
      (∫ A : Cfg, fCont A * Real.exp (-(beta * Y A B)) ∂muH) := by
  rw [p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B]
  calc
    (∫ A : Cfg, fCont A * K beta A B ∂muH) =
        ∫ A : Cfg, Real.exp (-beta * aB B) *
          (fCont A * Real.exp (-(beta * Y A B))) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AIC_originalKernel_factorization H beta A B]
      ring
    _ = Real.exp (-beta * aB B) *
        (∫ A : Cfg, fCont A * Real.exp (-(beta * Y A B)) ∂muH) := by
      rw [integral_const_mul]

/-- The actual centered cubic error, including the exact outer exponential.
This is a new auxiliary error of the unchanged transfer, not AIA's full-S R4. -/
def p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fCont A *
    (Real.exp (-beta * aB B) *
      p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) ∂muH

local notation "Rc4" => p4Q2PZ37AIC_originalFactoredFourthOrderRemainder H

theorem p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_integrable
    (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => fCont A *
      (Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B))) muH := by
  have hArg : Continuous (fun A : Cfg => beta * Y A B) :=
    continuous_const.mul (p4Q2PZ37AIC_originalCenteredAction_continuous H B)
  have hR : Continuous (fun A : Cfg =>
      p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) :=
    p4Q2PZ37AIC_expCubicRemainder_continuous.comp hArg
  exact ((p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.mul
    (continuous_const.mul hR)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Every source-weighted power of the actual centered action is integrable. -/
theorem p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable
    (n : ℕ) (B : Cfg) :
    Integrable (fun A : Cfg => fCont A * (Y A B) ^ n) muH := by
  have hCont : Continuous (fun A : Cfg => fCont A * (Y A B) ^ n) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous.mul
      ((p4Q2PZ37AIC_originalCenteredAction_continuous H B).pow n)
  exact hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Centering removes the crossing contribution from the first source moment. -/
theorem p4Q2PZ37AIC_originalCenteredAction_firstMoment (B : Cfg) :
    (∫ A : Cfg, fCont A * Y A B ∂muH) = Vsrc := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hX : Continuous (fun A : Cfg => X A B) :=
    p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B
  have i2 : Integrable (fun A : Cfg => (fCont A) ^ 2) muH :=
    (hf.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have iX : Integrable (fun A : Cfg => fCont A * X A B) muH :=
    (hf.mul hX).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hXzero : (∫ A : Cfg, fCont A * X A B ∂muH) = 0 := by
    simpa only [pow_one] using
      p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero H 1 B
  calc
    (∫ A : Cfg, fCont A * Y A B ∂muH) =
        ∫ A : Cfg, (fCont A) ^ 2 + fCont A * X A B ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      unfold p4Q2PZ37AIC_originalCenteredAction
      ring
    _ = (∫ A : Cfg, (fCont A) ^ 2 ∂muH) +
        (∫ A : Cfg, fCont A * X A B ∂muH) :=
      integral_add i2 iX
    _ = Vsrc := by
      simp only [hXzero, add_zero, p4Q2PZ37AHN_originalSource_HaarSecondMoment]

/-- The second source-weighted centered moment vanishes. The even mixed
term uses the separate AHS Ward cancellation retained in AHZ. -/
theorem p4Q2PZ37AIC_originalCenteredAction_secondMoment_zero (B : Cfg) :
    (∫ A : Cfg, fCont A * (Y A B) ^ 2 ∂muH) = 0 := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hX : Continuous (fun A : Cfg => X A B) :=
    p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B
  have hInt {g : Cfg → ℝ} (hg : Continuous g) : Integrable g muH :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i3 : Integrable (fun A : Cfg => (fCont A) ^ 3) muH :=
    hInt (hf.pow 3)
  have i2X : Integrable (fun A : Cfg => 2 * ((fCont A) ^ 2 * X A B)) muH :=
    (hInt ((hf.pow 2).mul hX)).const_mul 2
  have iX2 : Integrable (fun A : Cfg => fCont A * (X A B) ^ 2) muH :=
    hInt (hf.mul (hX.pow 2))
  have hCube : (∫ A : Cfg, (fCont A) ^ 3 ∂muH) = 0 :=
    p4Q2PZ37AHW2_originalSourceThirdMoment_zero H
  have h2X : (∫ A : Cfg, (fCont A) ^ 2 * X A B ∂muH) = 0 :=
    p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero H 2 B
  have hX2 : (∫ A : Cfg, fCont A * (X A B) ^ 2 ∂muH) = 0 :=
    p4Q2PZ37AHZ_originalSource_centeredCrossingSquareHaar_zero H B
  calc
    (∫ A : Cfg, fCont A * (Y A B) ^ 2 ∂muH) =
        ∫ A : Cfg, (fCont A) ^ 3 +
          2 * ((fCont A) ^ 2 * X A B) + fCont A * (X A B) ^ 2 ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      unfold p4Q2PZ37AIC_originalCenteredAction
      ring
    _ = (∫ A : Cfg, (fCont A) ^ 3 ∂muH) +
        2 * (∫ A : Cfg, (fCont A) ^ 2 * X A B ∂muH) +
        (∫ A : Cfg, fCont A * (X A B) ^ 2 ∂muH) := by
      have hSplit := integral_add (i3.add i2X) iX2
      simp only [Pi.add_apply] at hSplit
      rw [hSplit, integral_add i3 i2X, integral_const_mul]
    _ = 0 := by
      simp only [hCube, h2X, hX2, mul_zero, add_zero]

/-- The third source-weighted centered moment keeps the actual source
fourth moment and squared-source/crossing-square correlation. -/
theorem p4Q2PZ37AIC_originalCenteredAction_thirdMoment_exact (B : Cfg) :
    (∫ A : Cfg, fCont A * (Y A B) ^ 3 ∂muH) = Q4 + 3 * D B := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hX : Continuous (fun A : Cfg => X A B) :=
    p4Q2PZ37AHZ_originalCenteredCrossing_continuous H B
  have hInt {g : Cfg → ℝ} (hg : Continuous g) : Integrable g muH :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i4 : Integrable (fun A : Cfg => (fCont A) ^ 4) muH :=
    hInt (hf.pow 4)
  have i3X : Integrable (fun A : Cfg => 3 * ((fCont A) ^ 3 * X A B)) muH :=
    (hInt ((hf.pow 3).mul hX)).const_mul 3
  have i2X2 : Integrable (fun A : Cfg =>
      3 * ((fCont A) ^ 2 * (X A B) ^ 2)) muH :=
    (hInt ((hf.pow 2).mul (hX.pow 2))).const_mul 3
  have iX3 : Integrable (fun A : Cfg => fCont A * (X A B) ^ 3) muH :=
    hInt (hf.mul (hX.pow 3))
  have h3X : (∫ A : Cfg, (fCont A) ^ 3 * X A B ∂muH) = 0 :=
    p4Q2PZ37AHZ_originalSourcePower_centeredCrossingHaar_zero H 3 B
  have hX3 : (∫ A : Cfg, fCont A * (X A B) ^ 3 ∂muH) = 0 := by
    simpa only [pow_one] using
      p4Q2PZ37AHZ_originalSourcePower_centeredCrossingCubeHaar_zero H 1 B
  calc
    (∫ A : Cfg, fCont A * (Y A B) ^ 3 ∂muH) =
        ∫ A : Cfg, (fCont A) ^ 4 + 3 * ((fCont A) ^ 3 * X A B) +
          3 * ((fCont A) ^ 2 * (X A B) ^ 2) + fCont A * (X A B) ^ 3 ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      unfold p4Q2PZ37AIC_originalCenteredAction
      ring
    _ = (∫ A : Cfg, (fCont A) ^ 4 ∂muH) +
        3 * (∫ A : Cfg, (fCont A) ^ 3 * X A B ∂muH) +
        3 * (∫ A : Cfg, (fCont A) ^ 2 * (X A B) ^ 2 ∂muH) +
        (∫ A : Cfg, fCont A * (X A B) ^ 3 ∂muH) := by
      have hSplit2 := integral_add (i4.add i3X) i2X2
      have hSplit3 := integral_add ((i4.add i3X).add i2X2) iX3
      simp only [Pi.add_apply] at hSplit2 hSplit3
      rw [hSplit3, hSplit2, integral_add i4 i3X,
        integral_const_mul, integral_const_mul]
    _ = Q4 + 3 * D B := by
      simp only [h3X, hX3, mul_zero, add_zero,
        p4Q2PZ37AHZ_originalSourceFourthHaarMoment,
        p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment]

/-- The source times its actual centered cubic Taylor polynomial is
integrable for every real coupling, without a sign condition on Y. -/
theorem p4Q2PZ37AIC_originalCenteredCubicIntegrand_integrable
    (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => fCont A *
      (1 - beta * Y A B + (beta * Y A B) ^ 2 / 2 -
        (beta * Y A B) ^ 3 / 6)) muH := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have hArg : Continuous (fun A : Cfg => beta * Y A B) :=
    continuous_const.mul (p4Q2PZ37AIC_originalCenteredAction_continuous H B)
  have hPoly : Continuous (fun A : Cfg =>
      1 - beta * Y A B + (beta * Y A B) ^ 2 / 2 -
        (beta * Y A B) ^ 3 / 6) :=
    ((continuous_const.sub hArg).add ((hArg.pow 2).div_const 2)).sub
      ((hArg.pow 3).div_const 6)
  exact (hf.mul hPoly).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Exact source-weighted centered cubic polynomial integral, at every
real coupling. The quadratic term vanishes; the true Q4 and D remain. -/
theorem p4Q2PZ37AIC_originalCenteredCubicIntegral
    (beta : ℝ) (B : Cfg) :
    (∫ A : Cfg, fCont A *
      (1 - beta * Y A B + (beta * Y A B) ^ 2 / 2 -
        (beta * Y A B) ^ 3 / 6) ∂muH) =
      -beta * Vsrc - beta ^ 3 / 6 * (Q4 + 3 * D B) := by
  have hf : Continuous (fun A : Cfg => fCont A) :=
    (p4Q2PZ37AFZ_originalCenteredContinuous H).continuous
  have i0 : Integrable (fun A : Cfg => fCont A) muH :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hOne : Integrable (fun A : Cfg => fCont A * Y A B) muH := by
    simpa only [pow_one] using
      p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable H 1 B
  have i1 : Integrable (fun A : Cfg => (-beta) * (fCont A * Y A B)) muH :=
    hOne.const_mul (-beta)
  have i2 : Integrable (fun A : Cfg =>
      (beta ^ 2 / 2) * (fCont A * (Y A B) ^ 2)) muH :=
    (p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable H 2 B).const_mul
      (beta ^ 2 / 2)
  have i3 : Integrable (fun A : Cfg =>
      (-(beta ^ 3 / 6)) * (fCont A * (Y A B) ^ 3)) muH :=
    (p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable H 3 B).const_mul
      (-(beta ^ 3 / 6))
  calc
    (∫ A : Cfg, fCont A *
      (1 - beta * Y A B + (beta * Y A B) ^ 2 / 2 -
        (beta * Y A B) ^ 3 / 6) ∂muH) =
        ∫ A : Cfg, fCont A + (-beta) * (fCont A * Y A B) +
          (beta ^ 2 / 2) * (fCont A * (Y A B) ^ 2) +
          (-(beta ^ 3 / 6)) * (fCont A * (Y A B) ^ 3) ∂muH := by
      apply integral_congr_ae
      filter_upwards with A
      ring
    _ = (∫ A : Cfg, fCont A ∂muH) +
        (-beta) * (∫ A : Cfg, fCont A * Y A B ∂muH) +
        (beta ^ 2 / 2) * (∫ A : Cfg, fCont A * (Y A B) ^ 2 ∂muH) +
        (-(beta ^ 3 / 6)) * (∫ A : Cfg, fCont A * (Y A B) ^ 3 ∂muH) := by
      have hSplit2 := integral_add (i0.add i1) i2
      have hSplit3 := integral_add ((i0.add i1).add i2) i3
      simp only [Pi.add_apply] at hSplit2 hSplit3
      rw [hSplit3, hSplit2, integral_add i0 i1,
        integral_const_mul, integral_const_mul, integral_const_mul]
    _ = -beta * Vsrc - beta ^ 3 / 6 * (Q4 + 3 * D B) := by
      rw [p4Q2PZ37AHP_originalSource_mean_zero H,
        p4Q2PZ37AIC_originalCenteredAction_firstMoment H B,
        p4Q2PZ37AIC_originalCenteredAction_secondMoment_zero H B,
        p4Q2PZ37AIC_originalCenteredAction_thirdMoment_exact H B]
      ring

/-- Integrated centered cubic approximation with the exact boundary factor. -/
def p4Q2PZ37AIC_originalFactoredCubicApproximation
    (beta : ℝ) (B : Cfg) : ℝ :=
  Real.exp (-beta * aB B) *
    (-(beta * Vsrc) - (beta ^ 3 / 6) * (Q4 + 3 * D B))

local notation "Pc3" => p4Q2PZ37AIC_originalFactoredCubicApproximation H

/-- Equivalent placement of the same A-independent exponential factor. -/
theorem p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_const_mul
    (beta : ℝ) (B : Cfg) :
    Rc4 beta B = Real.exp (-beta * aB B) *
      (∫ A : Cfg, fCont A *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ∂muH) := by
  unfold p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
  calc
    (∫ A : Cfg, fCont A * (Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) ∂muH) =
      ∫ A : Cfg, Real.exp (-beta * aB B) *
        (fCont A * p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) ∂muH := by
          apply integral_congr_ae
          filter_upwards with A
          ring
    _ = Real.exp (-beta * aB B) *
        (∫ A : Cfg, fCont A *
          p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ∂muH) := by
      rw [integral_const_mul]

/-- Exact error of the unchanged physical transfer, for every real beta. -/
theorem p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub
    (beta : ℝ) (B : Cfg) :
    Rc4 beta B = T beta f0 B - Pc3 beta B := by
  have hK := p4Q2PZ37AHP_originalKernelWeightedSource_integrable H beta B
  have hP := p4Q2PZ37AIC_originalCenteredCubicIntegrand_integrable H beta B
  calc
    Rc4 beta B =
      ∫ A : Cfg, fCont A * K beta A B -
        Real.exp (-beta * aB B) *
          (fCont A * (1 - beta * Y A B + (beta * Y A B) ^ 2 / 2 -
            (beta * Y A B) ^ 3 / 6)) ∂muH := by
      unfold p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
      apply integral_congr_ae
      filter_upwards with A
      rw [p4Q2PZ37AIC_originalKernel_factorization H beta A B]
      unfold p4Q2PZ37AIC_expCubicRemainder
      ring
    _ = (∫ A : Cfg, fCont A * K beta A B ∂muH) -
        Real.exp (-beta * aB B) *
          (∫ A : Cfg, fCont A *
            (1 - beta * Y A B + (beta * Y A B) ^ 2 / 2 -
              (beta * Y A B) ^ 3 / 6) ∂muH) := by
      rw [integral_sub hK (hP.const_mul (Real.exp (-beta * aB B))),
        integral_const_mul]
    _ = T beta f0 B - Pc3 beta B := by
      rw [← p4Q2PZ37AHP_originalTransfer_eq_continuousIntegral H beta B,
        p4Q2PZ37AIC_originalCenteredCubicIntegral H beta B]
      unfold p4Q2PZ37AIC_originalFactoredCubicApproximation
      ring

/-- Genuine centered cubic expansion; all coefficients are original Haar integrals. -/
theorem p4Q2PZ37AIC_originalTransfer_centeredCubic_expansion
    (beta : ℝ) (B : Cfg) :
    T beta f0 B =
      Real.exp (-beta * aB B) *
        (-(beta * Vsrc) - (beta ^ 3 / 6) * (Q4 + 3 * D B)) +
          Rc4 beta B := by
  rw [p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub H beta B]
  unfold p4Q2PZ37AIC_originalFactoredCubicApproximation
  ring

/-- The exact constant factor remains on the negative variance signal. -/
theorem p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Pc3 beta B ≤ Real.exp (-beta * aB B) * (-(beta * Vsrc)) := by
  have hQ := p4Q2PZ37AHZ_originalSourceFourthHaarMoment_nonneg H
  have hD := p4Q2PZ37AHZ_originalSourceSquareCenteredCrossingSquareMoment_nonneg H B
  have hCube : 0 ≤ (beta ^ 3 / 6) * (Q4 + 3 * D B) := by positivity
  unfold p4Q2PZ37AIC_originalFactoredCubicApproximation
  exact mul_le_mul_of_nonneg_left (sub_le_self _ hCube) (Real.exp_pos _).le

/-- Strictly negative CENTER, not an unconditional actual-transfer sign. -/
theorem p4Q2PZ37AIC_originalFactoredCubicApproximation_neg
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) :
    Pc3 beta B < 0 := by
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hSignal : Real.exp (-beta * aB B) * (-(beta * Vsrc)) < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) (neg_neg_of_pos (mul_pos hbeta hV))
  exact (p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance
    H beta hbeta.le B).trans_lt hSignal

/-- The pointwise weight retained after factoring the original boundary constant.
The second argument of min is the unchanged original full action. -/
def p4Q2PZ37AIC_originalFactoredRemainderWeight
    (beta : ℝ) (A B : Cfg) : ℝ :=
  Real.exp (-beta * min (aB B) (S A B))

local notation "qWeight" => p4Q2PZ37AIC_originalFactoredRemainderWeight H

theorem p4Q2PZ37AIC_originalFactoredRemainderWeight_continuous
    (beta : ℝ) (B : Cfg) :
    Continuous (fun A : Cfg => qWeight beta A B) :=
  Real.continuous_exp.comp
    (continuous_const.mul
      (continuous_const.min
        (p4Q2PZ37AHP_originalFullAction_continuous H B)))

/-- Continuous weights times the retained exponential and the actual centered
fourth power are integrable under the unchanged original product Haar measure. -/
theorem p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable
    (g : Cfg → ℝ) (hg : Continuous g) (beta : ℝ) (B : Cfg) :
    Integrable (fun A : Cfg => g A * qWeight beta A B * (Y A B) ^ 4) muH :=
  ((hg.mul (p4Q2PZ37AIC_originalFactoredRemainderWeight_continuous H beta B)).mul
    ((p4Q2PZ37AIC_originalCenteredAction_continuous H B).pow 4)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Genuine positive-source / retained-exponential / centered-action correlation. -/
def p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fp A * qWeight beta A B * (Y A B) ^ 4 ∂muH

/-- Genuine negative-source / retained-exponential / centered-action correlation. -/
def p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment
    (beta : ℝ) (B : Cfg) : ℝ :=
  ∫ A : Cfg, fm A * qWeight beta A B * (Y A B) ^ 4 ∂muH

local notation "J4wp" => p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment H
local notation "J4wm" => p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment H

/-- Both correlated quartic moments are nonnegative for every real coupling.
No equality between their weighted masses is asserted. -/
theorem p4Q2PZ37AIC_originalWeightedCenteredFourthMoments_nonneg
    (beta : ℝ) (B : Cfg) :
    0 ≤ J4wp beta B ∧ 0 ≤ J4wm beta B := by
  have hWeight (A : Cfg) : 0 ≤ qWeight beta A B := Real.exp_nonneg _
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

/-- The actual centered kernel error with its exact outer factor has the
pointwise minimum-action bound, including at beta=0 and for signed Y. -/
theorem p4Q2PZ37AIC_originalFactoredKernelRemainder_interval
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    0 ≤ Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ∧
      Real.exp (-beta * aB B) *
        p4Q2PZ37AIC_expCubicRemainder (beta * Y A B) ≤
          qWeight beta A B * beta ^ 4 * (Y A B) ^ 4 / 24 := by
  have h := p4Q2PZ37AIC_expCubicRemainder_factored_interval
    beta (aB B) (Y A B) hbeta
  rw [← p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction
    H A B] at h
  exact h

/-- Negative source part below, positive source part above: both bounds retain
the actual centered quartic correlation and pointwise exponential weight. -/
theorem p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_weightedInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    -((beta ^ 4 / 24) * J4wm beta B) ≤ Rc4 beta B ∧
      Rc4 beta B ≤ (beta ^ 4 / 24) * J4wp beta B := by
  obtain ⟨hp, hm⟩ := p4Q2PZ37AHY_originalSourceParts_continuous H
  have hpInt := p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable H fp hp beta B
  have hmInt := p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable H fm hm beta B
  have hrInt := p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_integrable H beta B
  have hPoint (A : Cfg) := p4Q2PZ37AIA_real_signedNonnegativeError_interval
    (fCont A)
    (Real.exp (-beta * aB B) * p4Q2PZ37AIC_expCubicRemainder (beta * Y A B))
    (qWeight beta A B * beta ^ 4 * (Y A B) ^ 4 / 24)
    (p4Q2PZ37AIC_originalFactoredKernelRemainder_interval H beta hbeta A B)
  constructor
  · calc
      -((beta ^ 4 / 24) * J4wm beta B) =
          ∫ A : Cfg, -(beta ^ 4 / 24) *
            (fm A * qWeight beta A B * (Y A B) ^ 4) ∂muH := by
        rw [integral_const_mul]
        unfold p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment
        ring
      _ ≤ Rc4 beta B := by
        unfold p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
        apply integral_mono (hmInt.const_mul _) hrInt
        intro A
        calc
          -(beta ^ 4 / 24) * (fm A * qWeight beta A B * (Y A B) ^ 4) =
              -((|fCont A| - fCont A) / 2) *
                (qWeight beta A B * beta ^ 4 * (Y A B) ^ 4 / 24) := by
            unfold p4Q2PZ37AHY_originalSourceNegativePart
            ring
          _ ≤ fCont A *
              (Real.exp (-beta * aB B) *
                p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) := (hPoint A).1
  · calc
      Rc4 beta B ≤
          ∫ A : Cfg, (beta ^ 4 / 24) *
            (fp A * qWeight beta A B * (Y A B) ^ 4) ∂muH := by
        unfold p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
        apply integral_mono hrInt (hpInt.const_mul _)
        intro A
        calc
          fCont A *
              (Real.exp (-beta * aB B) *
                p4Q2PZ37AIC_expCubicRemainder (beta * Y A B)) ≤
              ((|fCont A| + fCont A) / 2) *
                (qWeight beta A B * beta ^ 4 * (Y A B) ^ 4 / 24) := (hPoint A).2
          _ = (beta ^ 4 / 24) * (fp A * qWeight beta A B * (Y A B) ^ 4) := by
            unfold p4Q2PZ37AHY_originalSourcePositivePart
            ring
      _ = (beta ^ 4 / 24) * J4wp beta B := integral_const_mul _ _

/-- The retained weight is bounded by the unchanged right spatial halfweight. -/
theorem p4Q2PZ37AIC_originalFactoredRemainderWeight_le_rightHalfweight
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    qWeight beta A B ≤ Real.exp (-beta * (W B / 2)) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (p4Q2PZ37AIC_originalMinAction_ge_rightHalfweight H A B)
    (neg_nonpos.mpr hbeta)

theorem p4Q2PZ37AIC_originalFactoredRemainderWeight_le_one
    (beta : ℝ) (hbeta : 0 ≤ beta) (A B : Cfg) :
    qWeight beta A B ≤ 1 := by
  have hw :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction_nonneg
      H 2 (by norm_num) B
  have he : Real.exp (-beta * (W B / 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hbeta)
      (div_nonneg hw (by norm_num))
  exact (p4Q2PZ37AIC_originalFactoredRemainderWeight_le_rightHalfweight
    H beta hbeta A B).trans he

/-- Exact original physical-transfer interval retaining both weighted correlations. -/
theorem p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Pc3 beta B - (beta ^ 4 / 24) * J4wm beta B ≤ T beta f0 B ∧
      T beta f0 B ≤ Pc3 beta B + (beta ^ 4 / 24) * J4wp beta B := by
  have hr := p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_weightedInterval
    H beta hbeta B
  rw [p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub H beta B] at hr
  constructor <;> linarith only [hr.1, hr.2]

/-- The lower endpoint cannot itself certify a positive original transfer. -/
theorem p4Q2PZ37AIC_originalCenteredQuarticLowerEndpoint_nonpos
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    Pc3 beta B - (beta ^ 4 / 24) * J4wm beta B ≤ 0 := by
  have hCenter := p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance
    H beta hbeta B
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hm := (p4Q2PZ37AIC_originalWeightedCenteredFourthMoments_nonneg H beta B).2
  have hCost : 0 ≤ (beta ^ 4 / 24) * J4wm beta B := by positivity
  have hSignal : Real.exp (-beta * aB B) * (-(beta * Vsrc)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      (neg_nonpos.mpr (mul_nonneg hbeta hV))
  exact (sub_le_self _ hCost).trans (hCenter.trans hSignal)

/-- Explicit conditional negativity, including the true negative cubic term.
No witness satisfying this weighted margin is assumed to have been constructed. -/
theorem p4Q2PZ37AIC_originalTransfer_negative_of_weightedCenteredQuarticMargin
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg)
    (hmargin : (beta ^ 4 / 24) * J4wp beta B <
      Real.exp (-beta * aB B) *
        (beta * Vsrc + (beta ^ 3 / 6) * (Q4 + 3 * D B))) :
    T beta f0 B < 0 := by
  have hu :=
    (p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval H beta hbeta B).2
  unfold p4Q2PZ37AIC_originalFactoredCubicApproximation at hu
  linarith only [hu, hmargin]

/-- A stronger sufficient condition keeps the exact variance signal's outer factor. -/
theorem p4Q2PZ37AIC_originalTransfer_negative_of_factoredVarianceMargin
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg)
    (hmargin : (beta ^ 4 / 24) * J4wp beta B <
      Real.exp (-beta * aB B) * (beta * Vsrc)) :
    T beta f0 B < 0 := by
  have hu :=
    (p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval H beta hbeta.le B).2
  have hc := p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance
    H beta hbeta.le B
  linarith only [hu, hc, hmargin]

/-- Unconditional interval at the SAME original fixed coupling. -/
theorem p4Q2PZ37AIC_originalFixedTransfer_centeredWeightedQuarticInterval
    (B : Cfg) :
    Pc3 beta0 B - (beta0 ^ 4 / 24) * J4wm beta0 B ≤ T beta0 f0 B ∧
      T beta0 f0 B ≤ Pc3 beta0 B + (beta0 ^ 4 / 24) * J4wp beta0 B :=
  p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B

/-- The original fixed-coupling sign remains conditional on a genuine weighted margin. -/
theorem p4Q2PZ37AIC_originalFixedTransfer_negative_of_weightedCenteredQuarticMargin
    (B : Cfg)
    (hmargin : (beta0 ^ 4 / 24) * J4wp beta0 B <
      Real.exp (-beta0 * aB B) *
        (beta0 * Vsrc + (beta0 ^ 3 / 6) * (Q4 + 3 * D B))) :
    T beta0 f0 B < 0 :=
  p4Q2PZ37AIC_originalTransfer_negative_of_weightedCenteredQuarticMargin
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le B hmargin

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIC_expCubicRemainder
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIC_expCubicRemainder_continuous
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIC_exp_pos_discountedCubicRemainder_interval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIC_expCubicRemainder_interval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AIC_expCubicRemainder_factored_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalBoundaryConstant
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction_abs_le_threeHalfCount
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalBoundaryConstant_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFullAction_eq_boundaryConstant_add_centeredAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalMinAction_ge_rightHalfweight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalKernel_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredKernel_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredKernelWeightedSource_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalTransfer_factorization
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredFourthOrderRemainder
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction_weightedPower_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction_firstMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction_secondMoment_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredAction_thirdMoment_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredCubicIntegrand_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredCubicIntegral
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredCubicApproximation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_const_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_eq_sub
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalTransfer_centeredCubic_expansion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredCubicApproximation_le_negativeVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredCubicApproximation_neg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredRemainderWeight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredRemainderWeight_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalWeightedCenteredFourth_integrable
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalPositiveWeightedCenteredFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalNegativeWeightedCenteredFourthMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalWeightedCenteredFourthMoments_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredKernelRemainder_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredFourthOrderRemainder_weightedInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredRemainderWeight_le_rightHalfweight
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFactoredRemainderWeight_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalTransfer_centeredWeightedQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalCenteredQuarticLowerEndpoint_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalTransfer_negative_of_weightedCenteredQuarticMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalTransfer_negative_of_factoredVarianceMargin
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFixedTransfer_centeredWeightedQuarticInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIC_originalFixedTransfer_negative_of_weightedCenteredQuarticMargin
