import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCovarianceCertifiedChordalBallV5_PZ37AER
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AES — exact physical SU(2) receiver-to-numerator modulus

AER established the genuine covariance half-amplitude radius from an
as-yet non-numerical original source-numerator modulus radius r_N.

Here we isolate the remaining quantitative input one level closer to
the actual unchanged Wilson receiver, without replacing the source.
The numerator N_e(z) is EXACTLY the original normalized compact SU(2)
Haar integral of the unchanged centered physical JQ link receiver,
weighted by the original SU(2) Wilson character chi(g).

If the ORIGINAL joint physical source receiver has full-boundary
D_H oscillation <= L_F D_H(z,w), and the ORIGINAL Wilson character
has absolute bound K_chi, then

  |N_e(z)-N_e(w)| <= (L_F*K_chi)*D_H(z,w).

The nonnegative receiver slope and character envelope are explicitly
assumed certificates here, not fabricated numerics or unconditional
estimates. Haar integration is over the same original normalized SU(2)
reference Haar, and the center source remains the ZW original
Gauss-law-centered Wilson physical source.

Combining this reduction with AER replaces the unknown qualitative
numerator radius by the CHECKABLE formula

  r_N = (lambda*C_e(a)/4)/(L_F*K_chi+1),
  delta_q = lambda^2*C_e(a)/(4*(M+lambda)),
  R = min(r_N, 1, delta_q/(L_q(H)+1)) > 0.

On the same original boundary D_H<R, |C_e(z)-C_e(w)|<=C_e(a)/2.
The unchanged genuine pair-Haar two-sign covariance moment retains
its explicit polynomial factor.

This is a conditional receiver modulus, not a verified actual receiver
Lipschitz constant. In particular no numerical radius, H-uniform
coercivity, GI threshold or continuum Yang--Mills gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A pointwise source-receiver oscillation and a Wilson character
envelope multiply, without assuming the receiver has fixed sign. -/
theorem p4Q2PZ37AES_realWeightedReceiverOscillation
    (u v t L K d : ℝ)
    (hU : |u-v| ≤ L*d) (hT : |t| ≤ K)
    (hLD : 0 ≤ L*d) (hK : 0 ≤ K) :
    |u*t-v*t| ≤ (L*K)*d := by
  have hProd : |u*t-v*t| = |u-v| * |t| := by
    have hFactor : u*t-v*t = (u-v)*t := by ring
    rw [hFactor, abs_mul]
  rw [hProd]
  calc
    |u-v| * |t| ≤ (L*d)*K :=
      mul_le_mul hU hT (abs_nonneg _) hLD
    _ = (L*K)*d := by ring

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AES_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AES_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AES_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AES_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AES_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AES_probability : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- ORIGINAL SU(2) Wilson-character numerical bound. The original
Wilson one-link energy is in [0,2], hence chi=1-E is in [-1,1].
No character norm assumption remains in the physical numerator route. -/
theorem p4Q2PZ37AES_originalWilsonCharacter_abs_le_one
    (g : G) : |chi g| ≤ (1 : ℝ) := by
  have h0 := specialUnitaryWilsonPlaquetteEnergy_nonneg
    (by norm_num : 0 < 2) g
  have h2 := specialUnitaryWilsonPlaquetteEnergy_le_two
    (by norm_num : 0 < 2) g
  change |(1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 g| ≤ 1
  apply abs_le.mpr
  constructor <;> linarith only [h0, h2]

/-- The ORIGINAL Wilson character is a real continuous map on the
actual compact SU(2), so its genuine supremum norm is finite. -/
noncomputable def p4Q2PZ37AES_originalWilsonCharacterContinuous : C(G, ℝ) :=
  ⟨chi, by
    change Continuous (fun g : G =>
      (1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 g)
    exact continuous_const.sub
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2)⟩

/-- The original Wilson character has an ACTUAL, not hypothetical,
finite compact SU(2) bound. Its norm is not evaluated numerically. -/
theorem p4Q2PZ37AES_originalWilsonCharacter_abs_le_compactNorm
    (g : G) :
    |chi g| ≤ ‖p4Q2PZ37AES_originalWilsonCharacterContinuous‖ := by
  have hUp :=
    ContinuousMap.apply_le_norm p4Q2PZ37AES_originalWilsonCharacterContinuous g
  have hLow :=
    ContinuousMap.neg_norm_le_apply p4Q2PZ37AES_originalWilsonCharacterContinuous g
  change chi g ≤ ‖p4Q2PZ37AES_originalWilsonCharacterContinuous‖ at hUp
  change -‖p4Q2PZ37AES_originalWilsonCharacterContinuous‖ ≤ chi g at hLow
  exact abs_le.mpr ⟨hLow, hUp⟩

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
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "Mq" =>
  Real.exp (b0 *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) /
    Real.sqrt (k ^ 3)
local notation "Lq" => (13 * b0) * Real.exp (13 * b0) * Mq

local instance p4Q2PZ37AES_links : Fintype Link := Fintype.ofFinite _

/-- True physical numerator SU(2) Haar integral inherits a
quantitative two-boundary D_H modulus from the ACTUAL centered
Gauss-law source receiver and original Wilson character. An
unverified L_F/K certificate remains visible in the premise. -/
theorem p4Q2PZ37AES_originalReceiverSlope_givesNumeratorSlope
    (e : Link) (LF K : ℝ) (hLF : 0 ≤ LF) (hK : 0 ≤ K)
    (hCharacter : ∀ g : G, |chi g| ≤ K)
    (hReceiver : ∀ z w : Pair, ∀ g : G,
      |F e z g - F e w g| ≤ LF * D z w) :
    ∀ z w : Pair, |N e z-N e w| ≤ (LF*K)*D z w := by
  have hChi : Continuous (fun g : G => chi g) := by
    change Continuous (fun g : G =>
      (1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 g)
    exact continuous_const.sub
      (continuous_specialUnitaryWilsonPlaquetteEnergy 2)
  intro z w
  have hIz : Integrable (fun g : G => F e z g * chi g) mu := by
    have hc : Continuous (fun g : G => F e z g * chi g) :=
      (F e z).continuous.mul hChi
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIw : Integrable (fun g : G => F e w g * chi g) mu := by
    have hc : Continuous (fun g : G => F e w g * chi g) :=
      (F e w).continuous.mul hChi
    exact hc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hDiff :
      N e z-N e w =
        ∫ g : G, (F e z g * chi g-F e w g * chi g) ∂mu := by
    change (∫ g : G, F e z g * chi g ∂mu) -
      (∫ g : G, F e w g * chi g ∂mu) = _
    exact (integral_sub hIz hIw).symm
  have hD : 0 ≤ D z w :=
    p4Q2PZ37ADL_originalFullDistance_nonneg H z w
  have hPt (g : G) :
      |F e z g*chi g-F e w g*chi g| ≤ (LF*K)*D z w :=
    p4Q2PZ37AES_realWeightedReceiverOscillation
      (F e z g) (F e w g) (chi g) LF K (D z w)
      (hReceiver z w g) (hCharacter g) (mul_nonneg hLF hD) hK
  have hIntegral :
      ‖∫ g : G, (F e z g*chi g-F e w g*chi g) ∂mu‖ ≤
        ((LF*K)*D z w) * (normalizedCompactHaar G).real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    filter_upwards with g
    rw [Real.norm_eq_abs]
    exact hPt g
  have hUniv : (normalizedCompactHaar G).real Set.univ = 1 := by simp
  calc
    |N e z-N e w| =
        ‖∫ g : G, (F e z g*chi g-F e w g*chi g) ∂mu‖ := by
          rw [← hDiff]
          exact (Real.norm_eq_abs _).symm
    _ ≤ (LF*K)*D z w := by
      simpa only [hUniv, mul_one] using hIntegral

/-- With the *proved* exact Wilson-character numerical bound 1,
only the genuine physical receiver slope LF is an outstanding premise.
The physical Haar numerator has the SAME full D_H slope LF. -/
theorem p4Q2PZ37AES_originalReceiverSlope_givesNumeratorUnitSlope
    (e : Link) (LF : ℝ) (hLF : 0 ≤ LF)
    (hReceiver : ∀ z w : Pair, ∀ g : G,
      |F e z g - F e w g| ≤ LF * D z w) :
    ∀ z w : Pair, |N e z-N e w| ≤ LF*D z w := by
  have h := p4Q2PZ37AES_originalReceiverSlope_givesNumeratorSlope
    H e LF 1 hLF (by norm_num)
    p4Q2PZ37AES_originalWilsonCharacter_abs_le_one hReceiver
  simpa only [mul_one] using h

/-- A measurable/pointwise genuine Wilson receiver oscillation certificate
replaces AER's abstract r_N by an exact radius formula. In particular
NO compactness existential for r_N appears in this conclusion.
Neither the slope LF nor the original character bound K is asserted
to have been evaluated. -/
theorem p4Q2PZ37AES_originalReceiverCertified_explicitStableBall
    (e : Link) (a : Pair) (lambda M LF K : ℝ)
    (ha : 0 < C b0 hb0 e a) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (hLF : 0 ≤ LF) (hK : 0 ≤ K)
    (hQFloor : ∀ z : Pair, lambda ≤ q b0 hb0 z)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hCharacter : ∀ g : G, |chi g| ≤ K)
    (hReceiver : ∀ z w : Pair, ∀ g : G,
      |F e z g-F e w g| ≤ LF*D z w) :
    ∃ R : ℝ,
      R = min ((lambda*C b0 hb0 e a/4)/(LF*K+1))
        (min 1
          ((lambda^2*C b0 hb0 e a/(4*(M+lambda)))/(Lq+1))) ∧
      0 < R ∧
      (∀ z w : Pair, D z w < R →
        |C b0 hb0 e z - C b0 hb0 e w| ≤ C b0 hb0 e a / 2) ∧
      (C b0 hb0 e a / 2)^2 *
        (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
          (8*Fintype.card Link)) ≤ S b0 hb0 e := by
  let LN : ℝ := LF*K
  let dN : ℝ := lambda*C b0 hb0 e a/4
  let rN : ℝ := dN/(LN+1)
  have hLN : 0 ≤ LN := mul_nonneg hLF hK
  have hdN : 0 < dN := by
    dsimp [dN]
    positivity
  have hDen : 0 < LN+1 := by linarith only [hLN]
  have hrN : 0 < rN := div_pos hdN hDen
  have hNumSlope :=
    p4Q2PZ37AES_originalReceiverSlope_givesNumeratorSlope
      H e LF K hLF hK hCharacter hReceiver
  have hNumMod : ∀ z w : Pair, D z w < rN →
      |N e z-N e w| ≤ dN := by
    intro z w hzw
    calc
      |N e z-N e w| ≤ LN*D z w := hNumSlope z w
      _ ≤ LN*rN := mul_le_mul_of_nonneg_left hzw.le hLN
      _ ≤ dN := p4Q2PZ37AER_realSlopeBudget LN dN hLN hdN.le
  obtain ⟨R, hRform, hRpos, hStable, hMoment⟩ :=
    p4Q2PZ37AER_originalCertifiedNumerator_explicitStableBall
      H e a lambda M rN ha hlambda hM hrN
      hQFloor hNmax hNumMod
  refine ⟨R, ?_, hRpos, hStable, hMoment⟩
  simpa only [rN, dN, LN] using hRform

/-- Specialize the true receiver-to-numerator radius with the
genuinely established SU(2) Wilson-character compact norm.
NO external character-bound hypothesis remains; only the physical
receiver D_H Lipschitz certificate LF is still conditional. -/
theorem p4Q2PZ37AES_originalReceiverSlope_explicitRadius_withTrueCharacterNorm
    (e : Link) (a : Pair) (lambda M LF : ℝ)
    (ha : 0 < C b0 hb0 e a) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (hLF : 0 ≤ LF)
    (hQFloor : ∀ z : Pair, lambda ≤ q b0 hb0 z)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hReceiver : ∀ z w : Pair, ∀ g : G,
      |F e z g - F e w g| ≤ LF*D z w) :
    ∃ R : ℝ,
      R = min ((lambda*C b0 hb0 e a/4)/
        (LF*‖p4Q2PZ37AES_originalWilsonCharacterContinuous‖+1))
        (min 1
          ((lambda^2*C b0 hb0 e a/(4*(M+lambda)))/(Lq+1))) ∧
      0 < R ∧
      (∀ z w : Pair, D z w < R →
        |C b0 hb0 e z - C b0 hb0 e w| ≤ C b0 hb0 e a / 2) ∧
      (C b0 hb0 e a / 2)^2 *
        (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
          (8*Fintype.card Link)) ≤ S b0 hb0 e := by
  exact p4Q2PZ37AES_originalReceiverCertified_explicitStableBall
    H e a lambda M LF
    ‖p4Q2PZ37AES_originalWilsonCharacterContinuous‖
    ha hlambda hM hLF (norm_nonneg _)
    hQFloor hNmax
    p4Q2PZ37AES_originalWilsonCharacter_abs_le_compactNorm
    hReceiver

/-- Use the verified ORIGINAL |chi|<=1 inequality to simplify
the AER physical covariance half-amplitude radius to a single true
source-receiver D_H slope LF, with no external character assumption. -/
theorem p4Q2PZ37AES_originalReceiverSlope_explicitRadius_unitCharacter
    (e : Link) (a : Pair) (lambda M LF : ℝ)
    (ha : 0 < C b0 hb0 e a) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (hLF : 0 ≤ LF)
    (hQFloor : ∀ z : Pair, lambda ≤ q b0 hb0 z)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hReceiver : ∀ z w : Pair, ∀ g : G,
      |F e z g - F e w g| ≤ LF*D z w) :
    ∃ R : ℝ,
      R = min ((lambda*C b0 hb0 e a/4)/(LF+1))
        (min 1
          ((lambda^2*C b0 hb0 e a/(4*(M+lambda)))/(Lq+1))) ∧
      0 < R ∧
      (∀ z w : Pair, D z w < R →
        |C b0 hb0 e z - C b0 hb0 e w| ≤ C b0 hb0 e a / 2) ∧
      (C b0 hb0 e a / 2)^2 *
        (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
          (8*Fintype.card Link)) ≤ S b0 hb0 e := by
  have h := p4Q2PZ37AES_originalReceiverCertified_explicitStableBall
    H e a lambda M LF 1 ha hlambda hM hLF (by norm_num)
    hQFloor hNmax p4Q2PZ37AES_originalWilsonCharacter_abs_le_one
    hReceiver
  simpa only [mul_one] using h

/-- The same legitimate original receiver certificate gives the
unchanged physical GI positive-mean consequence ONLY under the
separate original FC numerical dominance test. -/
theorem p4Q2PZ37AES_originalReceiverCertified_numericGivesGI
    (e : Link) (a : Pair) (lambda M LF K R : ℝ)
    (ha : 0 < C b0 hb0 e a) (hlambda : 0 < lambda)
    (hM : 0 ≤ M) (hLF : 0 ≤ LF) (hK : 0 ≤ K)
    (hQFloor : ∀ z : Pair, lambda ≤ q b0 hb0 z)
    (hNmax : ∀ z : Pair, |N e z| ≤ M)
    (hCharacter : ∀ g : G, |chi g| ≤ K)
    (hReceiver : ∀ z w : Pair, ∀ g : G,
      |F e z g-F e w g| ≤ LF*D z w)
    (hReq : R = min ((lambda*C b0 hb0 e a/4)/(LF*K+1))
      (min 1 ((lambda^2*C b0 hb0 e a/(4*(M+lambda)))/(Lq+1))))
    (hNumeric : (B b0 hb0)^2 <
      272*((C b0 hb0 e a/2)^2 *
        (2*(min (R/(2*(Fintype.card Link : ℝ)+1)) 2 / 4)^
          (8*Fintype.card Link)))) :
    0 < Budget b0 hb0 e := by
  obtain ⟨R0, hR0, _hPos, _hStable, hMoment⟩ :=
    p4Q2PZ37AES_originalReceiverCertified_explicitStableBall
      H e a lambda M LF K ha hlambda hM hLF hK
      hQFloor hNmax hCharacter hReceiver
  have heq : R = R0 := hReq.trans hR0.symm
  rw [heq] at hNumeric
  have hScale :=
    mul_le_mul_of_nonneg_left hMoment
      (show (0 : ℝ) ≤ 272 by norm_num)
  exact p4Q2PZ37ADE_fixedCovarianceFC_gives_positiveBudget
    H e (hNumeric.trans_le hScale)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AES_realWeightedReceiverOscillation
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AES_originalWilsonCharacter_abs_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AES_originalWilsonCharacter_abs_le_compactNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AES_originalReceiverSlope_givesNumeratorSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AES_originalReceiverSlope_givesNumeratorUnitSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AES_originalReceiverCertified_explicitStableBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AES_originalReceiverSlope_explicitRadius_withTrueCharacterNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AES_originalReceiverSlope_explicitRadius_unitCharacter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AES_originalReceiverCertified_numericGivesGI
