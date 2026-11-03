import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryExplicitFullSlopeV5_PZ37AEV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AEW — genuine physical receiver to explicit covariance Haar ball

AEV completely discharged AET's formerly conditional genuine source
receiver chordal modulus for each finite H, preserving the original
centered Gauss-law direction, original Wilson one-slab kernel, original
Perron vacuum and original SU(2) Haar measures.

We now insert that ACTUAL finite-H receiver slope into AES/AER's
explicit half-amplitude covariance radius, using AEK's unconditional
positive genuine JQ density floor. AED supplies an actual positive
covariance center for every original receiver link, while AEG supplies
the true finite-H maximum of the ORIGINAL Haar numerator.

The resulting fixed-H two-ball pair-Haar covariance square floor
is unconditional. The final GI/FC numerical dominance inequality,
H-uniform coercivity, physical spectral gap and continuum Yang--Mills
mass gap remain separate, unproved conditions.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AEW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AEW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AEW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AEW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AEW_borel : BorelSpace G :=
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
local notation "F" => p4Q2JQ_originalPhysicalSourceLinkReceiver H b0 hb0 f0
local notation "N" => p4Q2PZ37AEF_originalCenteredCovarianceNumerator H
local notation "q" => p4Q2JQ_originalPhysicalGIDensityWeight H
local notation "C" => p4Q2PZ37ACJ_originalCenteredEnergyCovariance H
local notation "S" => p4Q2PZ37ACJ_originalCenteredCovarianceSecondMoment H
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "B" => p4Q2PZ37ACJ_originalCenteredReceiverFCEnvelope H
local notation "Budget" => p4Q2PZ37ACO_originalGIMeanBudget H
local notation "O" =>
  normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) b0 hb0 f0
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "lambdaRho" => Real.sqrt (k^3)
local notation "Mrho" => Real.sqrt ((k⁻¹)^3)
local notation "Lrho" => (13*b0)*Real.exp (13*b0)*Mrho
local notation "MF" => ‖O‖
local notation "Msrc" =>
  p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "lambdaQ" => (1:ℝ)/Real.sqrt ((k⁻¹)^3)
local notation "Mq" =>
  Real.exp (b0 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
    Real.sqrt (k^3)
local notation "Lq" => (13*b0)*Real.exp (13*b0)*Mq

local instance p4Q2PZ37AEW_links : Fintype Link := Fintype.ofFinite _

/-- The complete source-dependent original receiver modulus, assembled
from AEU's left boundary and AEV's signed original Wilson-source
transfer right boundary, is a real, finite-H expression. -/
noncomputable def p4Q2PZ37AEW_originalReceiverFullSlope : ℝ :=
  (MF*Lrho/lambdaRho+2*MF) +
    ((((Tnorm⁻¹)^2)*((13*b0)*Msrc)+MF*Lrho)/lambdaRho+2*MF)

local notation "LF" => p4Q2PZ37AEW_originalReceiverFullSlope H

/-- Nonnegativity uses only the AEV/AEU proven coefficients. -/
theorem p4Q2PZ37AEW_originalReceiverFullSlope_nonneg : 0 ≤ LF := by
  unfold p4Q2PZ37AEW_originalReceiverFullSlope
  exact add_nonneg
    (p4Q2PZ37AEV_originalLeftCoefficient_nonneg H)
    (p4Q2PZ37AEV_originalRightCoefficient_nonneg H)

/-- ORIGINAL physical source-link receiver, all original left and
right boundary coordinates, no external regularity certificate. -/
theorem p4Q2PZ37AEW_originalReceiver_unconditionalFullSlope
    (e : Link) :
    ∀ (z w : Pair) (xi : G),
      |F e z xi-F e w xi| ≤ LF*D z w := by
  simpa only [p4Q2PZ37AEW_originalReceiverFullSlope] using
    (p4Q2PZ37AEV_originalReceiver_unconditionalFullBoundarySlope H e)

/-- The ORIGINAL SU(2) Haar Wilson-character covariance numerator
inherits the same fully proved physical D_H coefficient. -/
theorem p4Q2PZ37AEW_originalNumerator_unconditionalFullSlope
    (e : Link) :
    ∀ z w : Pair, |N e z-N e w| ≤ LF*D z w := by
  simpa only [p4Q2PZ37AEW_originalReceiverFullSlope] using
    (p4Q2PZ37AEV_originalNumerator_unconditionalFullBoundarySlope H e)

/-- AEK's original Wilson-action density bound is a TRUE explicit
strictly positive q_H floor for all physical pair boundaries. -/
theorem p4Q2PZ37AEW_originalJQDensity_explicitPositiveFloor :
    0 < lambdaQ ∧
      ∀ z : Pair, lambdaQ ≤ q b0 hb0 z := by
  obtain ⟨hlambda, hq⟩ :=
    p4Q2PZ37AEK_originalPhysicalDensity_explicitWilsonBounds H
  exact ⟨hlambda, fun z => (hq z).1⟩

/-- The remaining AER/AES local radius input is no longer any
unverified receiver regularity or density floor. For any actual
positive covariance center and any genuine numerator amplitude
majorant, the original finite-H half-amplitude radius and actual
original pair-Haar two-sign square moment are explicit. -/
theorem p4Q2PZ37AEW_originalCertified_explicitPhysicalStableBall
    (e : Link) (a : Pair) (M : ℝ)
    (ha : 0 < C b0 hb0 e a) (hM : 0 ≤ M)
    (hNmax : ∀ z : Pair, |N e z| ≤ M) :
    ∃ R : ℝ,
      R = min ((lambdaQ*C b0 hb0 e a/4)/(LF+1))
        (min 1
          ((lambdaQ^2*C b0 hb0 e a/(4*(M+lambdaQ)))/(Lq+1))) ∧
      0 < R ∧
      (∀ z w : Pair, D z w < R →
        |C b0 hb0 e z-C b0 hb0 e w| ≤ C b0 hb0 e a/2) ∧
      (C b0 hb0 e a/2)^2 *
        (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
          (8*Fintype.card Link)) ≤ S b0 hb0 e := by
  obtain ⟨hlambda, hqFloor⟩ :=
    p4Q2PZ37AEW_originalJQDensity_explicitPositiveFloor H
  exact p4Q2PZ37AES_originalReceiverSlope_explicitRadius_unitCharacter
    H e a lambdaQ M LF ha hlambda hM
    (p4Q2PZ37AEW_originalReceiverFullSlope_nonneg H)
    hqFloor hNmax
    (p4Q2PZ37AEW_originalReceiver_unconditionalFullSlope H e)

/-- All genuine physical source-receiver regularity, density-floor,
positive-center and Haar-numerator amplitude premises are discharged.
Only genuinely finite-H witnesses remain in the statement: a true
positive covariance center a, an actual original numerator ceiling M,
and the displayed explicit radius R. -/
theorem p4Q2PZ37AEW_originalEveryLink_explicitPhysicalBall_exists
    (e : Link) :
    ∃ a : Pair, 0 < C b0 hb0 e a ∧
      ∃ M R : ℝ, 0 < M ∧ 0 < R ∧
        R = min ((lambdaQ*C b0 hb0 e a/4)/(LF+1))
          (min 1
            ((lambdaQ^2*C b0 hb0 e a/(4*(M+lambdaQ)))/(Lq+1))) ∧
        (∀ z w : Pair, D z w < R →
          |C b0 hb0 e z-C b0 hb0 e w| ≤ C b0 hb0 e a/2) ∧
        (C b0 hb0 e a/2)^2 *
          (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
            (8*Fintype.card Link)) ≤ S b0 hb0 e := by
  obtain ⟨a, ha, _hMax⟩ :=
    p4Q2PZ37AED_originalPositiveMaximumCovariance_exists H e
  obtain ⟨M, hM, hNmax⟩ :=
    p4Q2PZ37AEG_originalNumerator_positiveMaxAbs_exists H e
  obtain ⟨R, hRform, hRpos, hStable, hMoment⟩ :=
    p4Q2PZ37AEW_originalCertified_explicitPhysicalStableBall
      H e a M ha hM.le hNmax
  exact ⟨a, ha, M, R, hM, hRpos, hRform, hStable, hMoment⟩

/-- The original finite-H FC numerical test remains transparent and
separate. AEV/AEW supply the entire genuine physical analytic radius
and Haar moment; ONLY the concrete numerical comparison is assumed. -/
theorem p4Q2PZ37AEW_originalExplicitPhysicalBall_numericGivesGI
    (e : Link) (a : Pair) (M R : ℝ)
    (ha : 0 < C b0 hb0 e a) (hM : 0 ≤ M)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hRform :
      R = min ((lambdaQ*C b0 hb0 e a/4)/(LF+1))
        (min 1
          ((lambdaQ^2*C b0 hb0 e a/(4*(M+lambdaQ)))/(Lq+1))))
    (hNumeric :
      (B b0 hb0)^2 <
        272*((C b0 hb0 e a/2)^2 *
          (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
            (8*Fintype.card Link)))) :
    0 < Budget b0 hb0 e := by
  obtain ⟨R0, hR0, _hRpos, _hStable, hMoment⟩ :=
    p4Q2PZ37AEW_originalCertified_explicitPhysicalStableBall
      H e a M ha hM hNmax
  have hR : R = R0 := hRform.trans hR0.symm
  rw [hR] at hNumeric
  have hScale :=
    mul_le_mul_of_nonneg_left hMoment
      (show (0 : ℝ) ≤ 272 by norm_num)
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget
    H e (hNumeric.trans_le hScale)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalReceiverFullSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalReceiver_unconditionalFullSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalNumerator_unconditionalFullSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalJQDensity_explicitPositiveFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalCertified_explicitPhysicalStableBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalEveryLink_explicitPhysicalBall_exists
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AEW_originalExplicitPhysicalBall_numericGivesGI
