import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverLocalToGlobalChordalV5_PZ37AET
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEU — unconditional original receiver left-link modulus

The ORIGINAL JQ physical receiver is the EXACT GN quotient

  F_e(A,B;xi) = ||T_H||^(-2) t_f0(B[e:=xi]) / rho_H(A,B[e:=xi]),

where t_f0 is the unchanged Wilson transfer integral of the genuine
centered Gauss-law source f0, and rho_H is the genuine positive joint
sqrt-density. The numerator has ZERO dependence on the left boundary A.

AEK proves a true positive finite-H floor lambda_rho for rho_H;
AEQ supplies an explicit original full D_H unit-ball rho Lipschitz
slope L_rho; the original JQ receiving BCF is a genuine bounded
continuous function with its actual norm M_F. Thus the ENTIRE left
boundary coordinate variation is quantitatively controlled without
any new source regularity assumption:

  L_left = M_F * L_rho / lambda_rho + 2*M_F,
  |F_e(A[i:=g],B;xi)-F_e(A[i:=h],B;xi)|
    <= L_left * d_J(g,h).

The first term controls d_J<=1 by exact quotient cancellation,
while the 2*M_F term handles d_J>1 using the true BCF amplitude norm.
All original physical objects, Haar measures and metrics are unchanged.

AET can now use L_left+L_right, assuming only the still missing
right non-receiver-link slope L_right. This reduces the remaining
physical obstruction to the right boundary source-transfer integral
and rho factors; it does NOT prove L_right, uniform-in-H coercivity,
a physical GI numerical threshold or continuum Yang--Mills gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- The genuinely identical numerator cancels in the true ratio,
with only the first denominator bounded below and an amplitude
ceiling at the second point. -/
theorem p4Q2PZ37AEU_realSameNumerator_ratioModulus
    (n a b lambda M delta : ℝ)
    (hlambda : 0 < lambda) (ha : lambda ≤ a)
    (hb : 0 < b)
    (hM : |n / b| ≤ M) (hDelta : |a-b| ≤ delta) :
    |n/a - n/b| ≤ M*delta/lambda := by
  have h := p4Q2PZ37AEF_realQuotientVariation_le
    n n a b lambda 0 delta M hlambda ha hb
    (by simp) hDelta hM
  simpa only [sub_self, abs_zero, zero_add] using h

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AEU_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEU_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEU_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEU_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEU_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "rho" => continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "O" =>
  normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) b0 hb0 f0
local notation "F" => p4Q2JQ_originalPhysicalSourceLinkReceiver H b0 hb0 f0
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "lambdaRho" => Real.sqrt (k^3)
local notation "Mrho" => Real.sqrt ((k⁻¹)^3)
local notation "c" => 13*b0
local notation "Lrho" => c*Real.exp c*Mrho
local notation "MF" => ‖O‖
local notation "Lleft" => (MF*Lrho/lambdaRho)+2*MF

local instance p4Q2PZ37AEU_links : Fintype Link := Fintype.ofFinite _

/-- The unchanged original physical receiver is bounded explicitly
by the genuine norm of its original BCF on the whole pair-boundary. -/
theorem p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
    (e : Link) (A B : Cfg) (xi : G) :
    |F e (A,B) xi| ≤ MF := by
  change |O (A, Function.update B e xi)| ≤ ‖O‖
  simpa only [Real.norm_eq_abs] using
    (BoundedContinuousFunction.norm_coe_le_norm O
      (A, Function.update B e xi))

/-- GN's exact source-transfer quotient on the SAME physical right
link insertion, NOT an independently introduced receiver. -/
theorem p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho
    (e : Link) (A B : Cfg) (xi : G) :
    F e (A,B) xi =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) b0 hb0‖⁻¹)^2 *
        decomposableOneSliceTransferIntegral H 2 b0 f0
          (Function.update B e xi) /
      rho (A,Function.update B e xi) := by
  change O (A, Function.update B e xi) = _
  exact p4Q2GN_originalReceiver_eq_transferIntegral
    H b0 hb0 f0 (A,Function.update B e xi)

/-- The original ADL two-boundary physical D_H reduces EXACTLY
to the same original SU(2) d_J under one left link change. -/
theorem p4Q2PZ37AEU_originalFullDistance_firstBoundary_oneLink
    (A B : Cfg) (i : Link) (g h : G) :
    D (Function.update A i g, B) (Function.update A i h, B) =
      dJ g h := by
  classical
  change (∑ j : Link,
      (dJ ((Function.update A i g) j) ((Function.update A i h) j) +
        dJ (B j) (B j))) = dJ g h
  simp only [p4Q2PZ37ADK_trueChordalDistance_self, add_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Function.update, hji, p4Q2PZ37ADK_trueChordalDistance]
  · simp

/-- AEK's real Wilson floor and AEQ's exact rho Lipschitz control
the entire LEFT boundary source receiver on the d_J unit ball.
The numerator is the SAME original source-transfer integral
at both configurations, so no source variation is assumed. -/
theorem p4Q2PZ37AEU_originalLeftOneLink_unitChordalSlope
    (e i : Link) (A B : Cfg) (g h xi : G)
    (hChord : dJ g h ≤ 1) :
    |F e (Function.update A i g,B) xi -
       F e (Function.update A i h,B) xi| ≤
      (MF*Lrho/lambdaRho) * dJ g h := by
  let Bg : Cfg := Function.update B e xi
  let Ag : Cfg := Function.update A i g
  let Ah : Cfg := Function.update A i h
  let zg : Pair := (Ag,Bg)
  let zh : Pair := (Ah,Bg)
  let n : ℝ :=
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 (by norm_num) b0 hb0‖⁻¹)^2 *
      decomposableOneSliceTransferIntegral H 2 b0 f0 Bg
  have hD : D zg zh = dJ g h :=
    p4Q2PZ37AEU_originalFullDistance_firstBoundary_oneLink H A Bg i g h
  have hDle : D zg zh ≤ 1 := by rw [hD]; exact hChord
  have hRhoMod :
      |rho zg-rho zh| ≤ Lrho * D zg zh := by
    have h := p4Q2PZ37AEQ_originalSqrtDensity_fullBall_localLipschitz
      H zg zh 1 hDle
    simpa only [mul_one] using h
  obtain ⟨hlam, hBounds⟩ :=
    p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H
  have hrhoz : lambdaRho ≤ rho zg := (hBounds zg).1
  have hrhoh : 0 < rho zh :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 zh
  have hFh : |n/rho zh| ≤ MF := by
    have h := p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
      H e Ah B xi
    rw [p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho] at h
    exact h
  have hRatio := p4Q2PZ37AEU_realSameNumerator_ratioModulus
    n (rho zg) (rho zh) lambdaRho MF (Lrho*D zg zh)
    hlam hrhoz hrhoh hFh hRhoMod
  have hFzg := p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho
    H e Ag B xi
  have hFzh := p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho
    H e Ah B xi
  calc
    |F e (Ag,B) xi-F e (Ah,B) xi| =
        |n/rho zg-n/rho zh| := by rw [hFzg, hFzh]
    _ ≤ MF*(Lrho*D zg zh)/lambdaRho := hRatio
    _ = (MF*Lrho/lambdaRho)*dJ g h := by rw [hD]; ring

/-- Genuine finite-H original physical receiver LEFT local slope,
with NO externally certified source variation. Long chords use the
real BCF amplitude and short chords use AEK/AEQ/GN. -/
theorem p4Q2PZ37AEU_originalLeftOneLink_unconditionalSlope
    (e i : Link) (A B : Cfg) (g h xi : G) :
    |F e (Function.update A i g,B) xi -
       F e (Function.update A i h,B) xi| ≤ Lleft*dJ g h := by
  have hMF : 0 ≤ MF := norm_nonneg _
  have hLrho : 0 ≤ Lrho := by
    dsimp only [Lrho]
    positivity
  have hlambda : 0 < lambdaRho :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).1
  have hBase : 0 ≤ MF*Lrho/lambdaRho :=
    div_nonneg (mul_nonneg hMF hLrho) hlambda.le
  have hCoeff : MF*Lrho/lambdaRho ≤ Lleft := by
    dsimp only [Lleft]
    linarith only [hMF]
  have hDist : 0 ≤ dJ g h :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  by_cases hSmall : dJ g h ≤ 1
  · calc
      |F e (Function.update A i g,B) xi -
          F e (Function.update A i h,B) xi| ≤
            (MF*Lrho/lambdaRho)*dJ g h :=
        p4Q2PZ37AEU_originalLeftOneLink_unitChordalSlope
          H e i A B g h xi hSmall
      _ ≤ Lleft*dJ g h :=
        mul_le_mul_of_nonneg_right hCoeff hDist
  · have hLarge : 1 ≤ dJ g h := le_of_lt (lt_of_not_ge hSmall)
    have hFg := p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
      H e (Function.update A i g) B xi
    have hFh := p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
      H e (Function.update A i h) B xi
    have hAmp : |F e (Function.update A i g,B) xi -
         F e (Function.update A i h,B) xi| ≤ 2*MF := by
      calc
        _ ≤ |F e (Function.update A i g,B) xi| +
          |F e (Function.update A i h,B) xi| := abs_sub_le _ _
        _ ≤ MF+MF := add_le_add hFg hFh
        _ = 2*MF := by ring
    have hScale : 2*MF ≤ (2*MF)*dJ g h := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hLarge
          (by positivity : 0 ≤ 2*MF))
    have hCoeff2 : 2*MF ≤ Lleft := by
      dsimp only [Lleft]
      linarith only [hBase]
    calc
      |F e (Function.update A i g,B) xi -
          F e (Function.update A i h,B) xi| ≤ 2*MF := hAmp
      _ ≤ (2*MF)*dJ g h := hScale
      _ ≤ Lleft*dJ g h :=
        mul_le_mul_of_nonneg_right hCoeff2 hDist

/-- AEU replaces AET's ENTIRE LEFT half of the original source
receiver local certificate by a genuine explicit finite-H constant.
ONLY non-receiver right-boundary local slopes remain conditional. -/
theorem p4Q2PZ37AEU_originalRightOnly_givesFullReceiverSlope
    (e : Link) (LR : ℝ) (hLR : 0 ≤ LR)
    (hRightAway : ∀ (A B : Cfg) (i : Link), i ≠ e →
      ∀ (g h xi : G),
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤ LR*dJ g h) :
    ∀ (z w : Pair) (xi : G),
      |F e z xi-F e w xi| ≤ (Lleft+LR)*D z w := by
  have hL : 0 ≤ Lleft := by
    have hMF : 0 ≤ MF := norm_nonneg _
    have hLrho : 0 ≤ Lrho := by dsimp only [Lrho]; positivity
    have hlam :=
      (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).1
    dsimp only [Lleft]
    exact add_nonneg
      (div_nonneg (mul_nonneg hMF hLrho) hlam.le)
      (mul_nonneg (by norm_num) hMF)
  apply p4Q2PZ37AET_originalOneLinkReceiver_givesFullSlope
    H e (Lleft+LR) (add_nonneg hL hLR)
  · intro A B i g h xi
    have h := p4Q2PZ37AEU_originalLeftOneLink_unconditionalSlope
      H e i A B g h xi
    exact h.trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_right hLR)
      (p4Q2PZ37ADK_trueChordalDistance_nonneg g h))
  · intro A B i hie g h xi
    exact (hRightAway A B i hie g h xi).trans
      (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hL)
        (p4Q2PZ37ADK_trueChordalDistance_nonneg g h))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AEU_realSameNumerator_ratioModulus
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEU_originalFullDistance_firstBoundary_oneLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEU_originalLeftOneLink_unitChordalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEU_originalLeftOneLink_unconditionalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEU_originalRightOnly_givesFullReceiverSlope
