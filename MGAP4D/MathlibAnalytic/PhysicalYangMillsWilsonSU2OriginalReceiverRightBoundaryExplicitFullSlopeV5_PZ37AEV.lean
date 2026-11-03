import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryTransferKernelSlopeV5_PZ37AEV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEV — full original centered physical receiver right-link slope

Compose the original signed source integral bound with AEU's EXACT
GN source-transfer/rho quotient, AEK's true positive rho floor,
AEQ's original full-boundary density modulus, and the true BCF norm.
The right receiver-link coordinate remains exactly invisible by AET.
This closes the remaining finite-H right-away receiver Lipschitz
premise without source regularization or replacement Haar law.

All constants are finite-volume genuine original-object expressions.
No numerical GI threshold, volume-uniform coercivity, positive
continuum Yang--Mills gap, or certified continuum limit is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "dJ" => p4Q2PZ37ADK_trueChordalDistance

local instance p4Q2PZ37AEV2_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEV2_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEV2_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEV2_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEV2_borel : BorelSpace G :=
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
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "a0" => (Tnorm⁻¹)^2
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "lambdaRho" => Real.sqrt (k^3)
local notation "Mrho" => Real.sqrt ((k⁻¹)^3)
local notation "Lrho" => (13*b0)*Real.exp (13*b0)*Mrho
local notation "MF" => ‖O‖
local notation "Msrc" =>
  p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "LT" => (13*b0)*Msrc
local notation "LN" => a0*LT
local notation "LRunit" => (LN + MF*Lrho)/lambdaRho
local notation "LR" => LRunit+2*MF
local notation "Lleft" => (MF*Lrho/lambdaRho)+2*MF

local instance p4Q2PZ37AEV2_links : Fintype Link := Fintype.ofFinite _

/-- The original full ADL distance is EXACTLY one true chord under a
single right boundary update, without treating the two boundaries
as independent measures. -/
theorem p4Q2PZ37AEV_originalFullDistance_rightBoundary_oneLink
    (A B : Cfg) (i : Link) (g h : G) :
    D (A,Function.update B i g) (A,Function.update B i h) =
      dJ g h := by
  classical
  change (∑ j : Link,
      (dJ (A j) (A j) +
        dJ ((Function.update B i g) j) ((Function.update B i h) j))) =
          dJ g h
  simp only [p4Q2PZ37ADK_trueChordalDistance_self, zero_add]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [Function.update, hji, p4Q2PZ37ADK_trueChordalDistance]
  · simp

/-- Receiver insertion and a distinct physical right coordinate
commute as actual typed configuration updates. -/
theorem p4Q2PZ37AEV_distinctRightUpdates_commute
    (B : Cfg) (i e : Link) (hie : i ≠ e) (g xi : G) :
    Function.update (Function.update B i g) e xi =
      Function.update (Function.update B e xi) i g := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [hie]
  · by_cases hje : j = e
    · subst j
      simp [Ne.symm hie]
    · simp [Function.update, hji, hje]

/-- The authentic source transfer normalization is nonnegative
and its Wilson-signed short-chord bound has a genuine finite-H
coefficient. -/
theorem p4Q2PZ37AEV_originalReceiver_rightUnitCoefficient_nonneg :
    0 ≤ LRunit := by
  have hMF : 0 ≤ MF := norm_nonneg _
  have hLrho : 0 ≤ Lrho :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
        (Real.exp_nonneg _))
      (Real.sqrt_nonneg _)
  have hLT : 0 ≤ LT :=
    mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
      (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)
  have hLN : 0 ≤ LN := mul_nonneg (sq_nonneg _) hLT
  have hlambda : 0 < lambdaRho :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).1
  exact div_nonneg
    (add_nonneg hLN (mul_nonneg hMF hLrho)) hlambda.le

/-- AEK+AEQ+AEF+AEU provide exact quotient cancellation for ALL
nonreceiver right links. The numerator variation is the integrated
ORIGINAL AEM Wilson-kernel variation against the SIGNED ZW source. -/
theorem p4Q2PZ37AEV_originalRightAway_unitChordSlope
    (e i : Link) (hie : i ≠ e)
    (A B : Cfg) (g h xi : G)
    (hChord : dJ g h ≤ 1) :
    |F e (A,Function.update B i g) xi -
      F e (A,Function.update B i h) xi| ≤
      LRunit * dJ g h := by
  let Bg : Cfg := Function.update (Function.update B i g) e xi
  let Bh : Cfg := Function.update (Function.update B i h) e xi
  let zg : Pair := (A,Bg)
  let zh : Pair := (A,Bh)
  have hCommG : Bg = Function.update (Function.update B e xi) i g :=
    p4Q2PZ37AEV_distinctRightUpdates_commute H B i e hie g xi
  have hCommH : Bh = Function.update (Function.update B e xi) i h :=
    p4Q2PZ37AEV_distinctRightUpdates_commute H B i e hie h xi
  have hD : D zg zh = dJ g h := by
    dsimp [zg,zh]
    rw [hCommG, hCommH]
    exact p4Q2PZ37AEV_originalFullDistance_rightBoundary_oneLink
      H A (Function.update B e xi) i g h
  have hDle : D zg zh ≤ 1 := by rw [hD]; exact hChord
  have hRho :
      |rho zg-rho zh| ≤ Lrho*dJ g h := by
    have h := p4Q2PZ37AEQ_originalSqrtDensity_fullBall_localLipschitz
      H zg zh 1 hDle
    simpa only [mul_one, hD] using h
  have hTransfer :
      |t Bg-t Bh| ≤ LT*dJ g h := by
    rw [hCommG, hCommH]
    exact p4Q2PZ37AEV_originalCenteredTransfer_rightOneLinkChordSlope
      H (Function.update B e xi) i g h
  have hAnorm : 0 ≤ a0 := sq_nonneg _
  have hNumerator :
      |a0*t Bg-a0*t Bh| ≤ LN*dJ g h := by
    calc
      |a0*t Bg-a0*t Bh| = a0*|t Bg-t Bh| := by
        rw [show a0*t Bg-a0*t Bh = a0*(t Bg-t Bh) by ring,
          abs_mul, abs_of_nonneg hAnorm]
      _ ≤ a0*(LT*dJ g h) :=
        mul_le_mul_of_nonneg_left hTransfer hAnorm
      _ = LN*dJ g h := by ring
  obtain ⟨hlambda, hBounds⟩ :=
    p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H
  have hFloor : lambdaRho ≤ rho zg := (hBounds zg).1
  have hPos : 0 < rho zh :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 zh
  have hM : |a0*t Bh/rho zh| ≤ MF := by
    have h := p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
      H e A (Function.update B i h) xi
    rw [p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho] at h
    exact h
  have hRatio :=
    p4Q2PZ37AEF_realQuotientVariation_le
      (a0*t Bg) (a0*t Bh) (rho zg) (rho zh)
      lambdaRho (LN*dJ g h) (Lrho*dJ g h) MF
      hlambda hFloor hPos hNumerator hRho hM
  have hFg := p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho
    H e A (Function.update B i g) xi
  have hFh := p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho
    H e A (Function.update B i h) xi
  calc
    |F e (A,Function.update B i g) xi -
      F e (A,Function.update B i h) xi| =
        |a0*t Bg/rho zg-a0*t Bh/rho zh| := by
          rw [hFg, hFh]
    _ ≤ (LN*dJ g h + MF*(Lrho*dJ g h))/lambdaRho := hRatio
    _ = LRunit*dJ g h := by ring

/-- True ALL-CHORD right-away receiver slope. Short chords use the
physical signed Wilson-transfer integral, long chords the actual
finite original BCF norm. No external right-away slope input. -/
theorem p4Q2PZ37AEV_originalRightAway_unconditionalSlope
    (e i : Link) (hie : i ≠ e)
    (A B : Cfg) (g h xi : G) :
    |F e (A,Function.update B i g) xi -
      F e (A,Function.update B i h) xi| ≤ LR*dJ g h := by
  have hMF : 0 ≤ MF := norm_nonneg _
  have hUnit : 0 ≤ LRunit :=
    p4Q2PZ37AEV_originalReceiver_rightUnitCoefficient_nonneg H
  have hDist : 0 ≤ dJ g h :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  by_cases hSmall : dJ g h ≤ 1
  · have hCoeff : LRunit ≤ LR := by
      change LRunit ≤ LRunit + 2*MF
      linarith only [hMF]
    calc
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤
          LRunit*dJ g h :=
        p4Q2PZ37AEV_originalRightAway_unitChordSlope
          H e i hie A B g h xi hSmall
      _ ≤ LR*dJ g h := mul_le_mul_of_nonneg_right hCoeff hDist
  · have hLarge : 1 ≤ dJ g h := le_of_lt (lt_of_not_ge hSmall)
    have hFg := p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
      H e A (Function.update B i g) xi
    have hFh := p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm
      H e A (Function.update B i h) xi
    have hAmp :
        |F e (A,Function.update B i g) xi -
          F e (A,Function.update B i h) xi| ≤ 2*MF := by
      calc
        _ ≤ |F e (A,Function.update B i g) xi| +
          |F e (A,Function.update B i h) xi| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le
              (F e (A,Function.update B i g) xi)
              (-(F e (A,Function.update B i h) xi)))
        _ ≤ MF+MF := add_le_add hFg hFh
        _ = 2*MF := by ring
    have hScale : 2*MF ≤ (2*MF)*dJ g h := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hLarge
          (mul_nonneg (by norm_num) hMF))
    have hCoeff : 2*MF ≤ LR := by
      change 2*MF ≤ LRunit + 2*MF
      linarith only [hUnit]
    calc
      |F e (A,Function.update B i g) xi -
        F e (A,Function.update B i h) xi| ≤ 2*MF := hAmp
      _ ≤ (2*MF)*dJ g h := hScale
      _ ≤ LR*dJ g h :=
        mul_le_mul_of_nonneg_right hCoeff hDist

theorem p4Q2PZ37AEV_originalRightCoefficient_nonneg :
    0 ≤ LR := by
  have hM : 0 ≤ MF := norm_nonneg _
  have hU := p4Q2PZ37AEV_originalReceiver_rightUnitCoefficient_nonneg H
  exact add_nonneg hU (mul_nonneg (by norm_num) hM)

theorem p4Q2PZ37AEV_originalLeftCoefficient_nonneg :
    0 ≤ Lleft := by
  have hMF : 0 ≤ MF := norm_nonneg _
  have hLrho : 0 ≤ Lrho :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
        (Real.exp_nonneg _))
      (Real.sqrt_nonneg _)
  have hlambda : 0 < lambdaRho :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).1
  exact add_nonneg
    (div_nonneg (mul_nonneg hMF hLrho) hlambda.le)
    (mul_nonneg (by norm_num) hMF)

/-- AEU's last physical certificate is DISCHARGED: all actual
finite-H original receiver boundary coordinates obey an explicit
global ADL D_H Lipschitz bound. The receiver link itself is exactly
invariant under AET. -/
theorem p4Q2PZ37AEV_originalReceiver_unconditionalFullBoundarySlope
    (e : Link) :
    ∀ (z w : Pair) (xi : G),
      |F e z xi-F e w xi| ≤ (Lleft+LR)*D z w := by
  apply p4Q2PZ37AEU_originalRightOnly_givesFullReceiverSlope
    H e LR (p4Q2PZ37AEV_originalRightCoefficient_nonneg H)
  intro A B i hie g h xi
  exact p4Q2PZ37AEV_originalRightAway_unconditionalSlope
    H e i hie A B g h xi

/-- The ORIGINAL signed SU(2) character Haar covariance numerator
inherits the exact same unconditional full D_H coefficient. -/
theorem p4Q2PZ37AEV_originalNumerator_unconditionalFullBoundarySlope
    (e : Link) :
    ∀ z w : Pair, |N e z-N e w| ≤ (Lleft+LR)*D z w := by
  exact p4Q2PZ37AES_originalReceiverSlope_givesNumeratorUnitSlope
    H e (Lleft+LR)
    (add_nonneg
      (p4Q2PZ37AEV_originalLeftCoefficient_nonneg H)
      (p4Q2PZ37AEV_originalRightCoefficient_nonneg H))
    (p4Q2PZ37AEV_originalReceiver_unconditionalFullBoundarySlope H e)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalFullDistance_rightBoundary_oneLink
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_distinctRightUpdates_commute
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalReceiver_rightUnitCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalRightAway_unitChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalRightAway_unconditionalSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalRightCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalLeftCoefficient_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalReceiver_unconditionalFullBoundarySlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEV_originalNumerator_unconditionalFullBoundarySlope
