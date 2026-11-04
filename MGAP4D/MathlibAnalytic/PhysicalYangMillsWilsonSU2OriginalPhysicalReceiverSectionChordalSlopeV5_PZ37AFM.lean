import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFourModeSharpChordalLipschitzV5_PZ37AFL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalReceiverRightBoundaryExplicitFullSlopeV5_PZ37AEV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFM — genuine centered Wilson/Perron transfer-section chordal slope

AFL eliminated the external SU(2) character envelope and character slope.
The remaining AFL receiver is the ACTUAL signed FF response
  F_z(g) = Tnorm^-1 * T_f(B) - P_z * U_z(g),  P_z > 0,
  U_z(g) = T_f(B[e := g]) / rho(A, B[e := g]).
The intermediate U is NOT itself AFL's original FF response.

This module derives a finite-H envelope and unconditional chordal slope
for U itself. The numerator uses the proven AEV original signed-source
kernel-integral variation; the denominator uses the original AEQ full
boundary Perron half-density variation and AEK positive Wilson floor.
The true JQ bounded continuous physical receiver supplies a uniform
numerator/denominator QUOTIENT envelope through its exact GN/AEU identity.

ABZ's exact affine identity and unchanged true FF BCF norm then remove
ALL external FF receiver envelope/slope fields from AFL's typed original
Haar-cell certificate. Rational samples stay on F (not U); original SU(2)
cell geometry and verified quadrature data remain unchanged.

No physical sample, Haar cell mass, sign crossing, volume-uniform
coercivity, spectral gap, or continuum Yang--Mills gap is asserted.
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

local instance p4Q2PZ37AFM_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFM_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFM_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFM_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFM_borel : BorelSpace G :=
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
local notation "rho" =>
  continuousJointSqrtDensity H 2 (by norm_num) b0 hb0
local notation "t" => decomposableOneSliceTransferIntegral H 2 b0 f0
local notation "U" =>
  p4Q2PZ37ABZ_originalTransferSection H b0 hb0 f0
local notation "F" =>
  p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0
local notation "P" =>
  p4Q2PZ37ABZ_originalTransferSectionPrefactor H b0 hb0
local notation "FJQ" =>
  p4Q2JQ_originalPhysicalSourceLinkReceiver H b0 hb0 f0
local notation "O" =>
  normalizedPhysicalOneSlabJointReceiverProductBCF H 2 (by norm_num) b0 hb0 f0
local notation "M" => ‖O‖
local notation "Tnorm" =>
  ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) b0 hb0‖
local notation "a0" => (Tnorm⁻¹)^2
local notation "Msrc" =>
  p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass H
local notation "LT" => (13*b0)*Msrc
local notation "k" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H b0
local notation "lambdaRho" => Real.sqrt (k^3)
local notation "Mrho" => Real.sqrt ((k⁻¹)^3)
local notation "Lrho" => (13*b0)*Real.exp (13*b0)*Mrho
local notation "MU" => M/a0
local notation "Lunit" => (LT+MU*Lrho)/lambdaRho
local notation "LU" => Lunit+2*MU
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H

local instance p4Q2PZ37AFM_links : Fintype Link := Fintype.ofFinite _

/-- The existing genuine physical transfer operator has positive norm,
so its inverse-square normalization is strictly positive. -/
theorem p4Q2PZ37AFM_originalTransferInvSq_pos : 0 < a0 := by
  have ht : 0 < Tnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) b0 hb0
  exact pow_pos (inv_pos.mpr ht) _

/-- The JQ true physical BCF receiver is exactly the ORIGINAL
ABZ transfer section times its inverse-square transfer norm. -/
theorem p4Q2PZ37AFM_originalJQReceiver_eq_scaledTransferSection
    (e : Link) (z : Pair) (g : G) :
    FJQ e z g = a0 * U e z g := by
  calc
    FJQ e z g =
        a0 * t (Function.update z.2 e g) /
          rho (z.1, Function.update z.2 e g) :=
      p4Q2PZ37AEU_originalReceiver_eq_sourceTransfer_div_rho H e z.1 z.2 g
    _ = a0 * U e z g := by
      unfold p4Q2PZ37ABZ_originalTransferSection
      ring

/-- Entire fixed-H transfer section has a uniform, genuine
physical BCF envelope. No independent envelope oracle is used. -/
theorem p4Q2PZ37AFM_originalTransferSection_abs_le_trueEnvelope
    (e : Link) (z : Pair) (g : G) :
    |U e z g| ≤ MU := by
  have ha0 : 0 < a0 := p4Q2PZ37AFM_originalTransferInvSq_pos H
  have hF : |FJQ e z g| ≤ M :=
    p4Q2PZ37AEU_originalReceiver_abs_le_trueBCFNorm H e z.1 z.2 g
  rw [p4Q2PZ37AFM_originalJQReceiver_eq_scaledTransferSection H e z g,
    abs_mul, abs_of_pos ha0] at hF
  exact (le_div_iff₀ ha0).2 (by nlinarith only [hF])

theorem p4Q2PZ37AFM_originalTransferSectionEnvelope_nonneg :
    0 ≤ MU := by
  exact div_nonneg (norm_nonneg _) (p4Q2PZ37AFM_originalTransferInvSq_pos H).le

theorem p4Q2PZ37AFM_originalUnitSlope_nonneg :
    0 ≤ Lunit := by
  have hLT : 0 ≤ LT :=
    mul_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
      (p4Q2PZ37AEV_originalCenteredSourceHaarL1Mass_nonneg H)
  have hLrho : 0 ≤ Lrho :=
    mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 13) hb0)
        (Real.exp_nonneg _))
      (Real.sqrt_nonneg _)
  have hMU : 0 ≤ MU :=
    p4Q2PZ37AFM_originalTransferSectionEnvelope_nonneg H
  have hlam : 0 < lambdaRho :=
    (p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H).1
  exact div_nonneg
    (add_nonneg hLT (mul_nonneg hMU hLrho)) hlam.le

/-- TRUE original Wilson signed-source transfer numerator and TRUE
joint Perron denominator yield a quotient estimate on unit chords. -/
theorem p4Q2PZ37AFM_originalTransferSection_unitChordSlope
    (e : Link) (z : Pair) (g h : G)
    (hChord : dJ g h ≤ 1) :
    |U e z g - U e z h| ≤ Lunit*dJ g h := by
  let Bg : Cfg := Function.update z.2 e g
  let Bh : Cfg := Function.update z.2 e h
  let zg : Pair := (z.1,Bg)
  let zh : Pair := (z.1,Bh)
  have hD : D zg zh = dJ g h :=
    p4Q2PZ37AEV_originalFullDistance_rightBoundary_oneLink
      H z.1 z.2 e g h
  have hDle : D zg zh ≤ 1 := by rw [hD]; exact hChord
  have hRho : |rho zg-rho zh| ≤ Lrho*dJ g h := by
    have h := p4Q2PZ37AEQ_originalSqrtDensity_fullBall_localLipschitz
      H zg zh 1 hDle
    simpa only [mul_one, hD] using h
  have hT : |t Bg-t Bh| ≤ LT*dJ g h :=
    p4Q2PZ37AEV_originalCenteredTransfer_rightOneLinkChordSlope
      H z.2 e g h
  obtain ⟨hlam, hBounds⟩ :=
    p4Q2PZ37AEK_originalJointSqrtDensity_explicitWilsonBounds H
  have hFloor : lambdaRho ≤ rho zg := (hBounds zg).1
  have hPos : 0 < rho zh :=
    continuousJointSqrtDensity_pos H 2 (by norm_num) b0 hb0 zh
  have hM : |t Bh/rho zh| ≤ MU := by
    change |U e z h| ≤ MU
    exact p4Q2PZ37AFM_originalTransferSection_abs_le_trueEnvelope H e z h
  have hRatio :=
    p4Q2PZ37AEF_realQuotientVariation_le
      (t Bg) (t Bh) (rho zg) (rho zh)
      lambdaRho (LT*dJ g h) (Lrho*dJ g h) MU
      hlam hFloor hPos hT hRho hM
  calc
    |U e z g-U e z h| =
        |t Bg/rho zg-t Bh/rho zh| := by rfl
    _ ≤ (LT*dJ g h+MU*(Lrho*dJ g h))/lambdaRho := hRatio
    _ = Lunit*dJ g h := by ring

/-- Long chords require no local density modulus: boundedness of
the SAME continuous physical receiver closes the gap. -/
theorem p4Q2PZ37AFM_originalTransferSection_unconditionalChordSlope
    (e : Link) (z : Pair) (g h : G) :
    |U e z g-U e z h| ≤ LU*dJ g h := by
  have hMU : 0 ≤ MU :=
    p4Q2PZ37AFM_originalTransferSectionEnvelope_nonneg H
  have hUnit : 0 ≤ Lunit := p4Q2PZ37AFM_originalUnitSlope_nonneg H
  have hD : 0 ≤ dJ g h :=
    p4Q2PZ37ADK_trueChordalDistance_nonneg g h
  by_cases hSmall : dJ g h ≤ 1
  · have hCoeff : Lunit ≤ LU := by
      change Lunit ≤ Lunit+2*MU
      linarith only [hMU]
    calc
      |U e z g-U e z h| ≤ Lunit*dJ g h :=
        p4Q2PZ37AFM_originalTransferSection_unitChordSlope
          H e z g h hSmall
      _ ≤ LU*dJ g h :=
        mul_le_mul_of_nonneg_right hCoeff hD
  · have hLarge : 1 ≤ dJ g h :=
      le_of_lt (lt_of_not_ge hSmall)
    have hg := p4Q2PZ37AFM_originalTransferSection_abs_le_trueEnvelope
      H e z g
    have hh := p4Q2PZ37AFM_originalTransferSection_abs_le_trueEnvelope
      H e z h
    have hAmp : |U e z g-U e z h| ≤ 2*MU := by
      calc
        _ ≤ |U e z g|+|U e z h| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (U e z g) (-(U e z h)))
        _ ≤ MU+MU := add_le_add hg hh
        _ = 2*MU := by ring
    have hScale : 2*MU ≤ (2*MU)*dJ g h := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hLarge
          (mul_nonneg (by norm_num) hMU))
    have hCoeff : 2*MU ≤ LU := by
      change 2*MU ≤ Lunit+2*MU
      linarith only [hUnit]
    calc
      |U e z g-U e z h| ≤ 2*MU := hAmp
      _ ≤ (2*MU)*dJ g h := hScale
      _ ≤ LU*dJ g h :=
        mul_le_mul_of_nonneg_right hCoeff hD

theorem p4Q2PZ37AFM_originalTransferSectionSlope_nonneg :
    0 ≤ LU := by
  exact add_nonneg (p4Q2PZ37AFM_originalUnitSlope_nonneg H)
    (mul_nonneg (by norm_num)
      (p4Q2PZ37AFM_originalTransferSectionEnvelope_nonneg H))


/-- The original receiver in AFL is the actual signed FF
response, an affine transform of the transfer-section quotient. -/
theorem p4Q2PZ37AFM_originalFF_eq_affineTransferSection
    (e : Link) (z : Pair) (g : G) :
    F e z g = Tnorm⁻¹*t z.2-P z*U e z g := by
  exact p4Q2PZ37ABZ_originalResponse_eq_transferSection H b0 hb0 f0 e z g

/-- Use the norm of the SAME bounded continuous FF response,
not the JQ receiver and not an externally chosen envelope. -/
noncomputable def p4Q2PZ37AFM_originalFFEnvelope (e : Link) : ℝ :=
  ‖p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
    H 2 (by norm_num) b0 hb0 f0 e‖
local notation "MFF" => p4Q2PZ37AFM_originalFFEnvelope H

theorem p4Q2PZ37AFM_originalFFEnvelope_nonneg (e : Link) :
    0 ≤ MFF e := by
  exact norm_nonneg _

theorem p4Q2PZ37AFM_originalFF_abs_le_trueBCFNorm
    (e : Link) (z : Pair) (g : G) :
    |F e z g| ≤ MFF e := by
  change
    |(p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
      H 2 (by norm_num) b0 hb0 f0 e) (z,g)| ≤
      ‖p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) b0 hb0 f0 e‖
  simpa only [Real.norm_eq_abs] using
    (BoundedContinuousFunction.norm_coe_le_norm
      (p4Q2FF_originalWilsonRelativeSignedLinkResponseBCF
        H 2 (by norm_num) b0 hb0 f0 e) (z,g))

/-- Difference of actual FF responses is P_z times the variation
of U, with the original unupdated source term cancelling. -/
theorem p4Q2PZ37AFM_originalFF_unconditionalChordSlope
    (e : Link) (z : Pair) (g h : G) :
    |F e z g-F e z h| ≤ (P z*LU)*dJ g h := by
  have hp : 0 < P z :=
    p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b0 hb0 z
  have hDiff :
      F e z g-F e z h = P z*(U e z h-U e z g) := by
    rw [p4Q2PZ37AFM_originalFF_eq_affineTransferSection H e z g,
      p4Q2PZ37AFM_originalFF_eq_affineTransferSection H e z h]
    ring
  calc
    |F e z g-F e z h| = P z*|U e z h-U e z g| := by
      rw [hDiff, abs_mul, abs_of_pos hp]
    _ = P z*|U e z g-U e z h| := by
      rw [abs_sub_comm]
    _ ≤ P z*(LU*dJ g h) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AFM_originalTransferSection_unconditionalChordSlope
          H e z g h) hp.le
    _ = (P z*LU)*dJ g h := by ring

theorem p4Q2PZ37AFM_originalFFSlope_nonneg
    (z : Pair) : 0 ≤ P z*LU := by
  exact mul_nonneg
    (p4Q2PZ37ABZ_originalTransferSectionPrefactor_pos H b0 hb0 z).le
    (p4Q2PZ37AFM_originalTransferSectionSlope_nonneg H)

/-- Final numerical-only certificate: there are NO physical receiver
bound/slope parameters, NO arbitrary character constants, and NO
replacement for true Haar cells or actual rational samples. -/
structure p4Q2PZ37AFM_originalNumericOnlyCellSamples
    (e : Link) (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  partition : p4Q2PZ37AFJ_originalHaarCells
  center : Fin partition.n → G
  radius : ℝ
  hRadius : 0 ≤ radius
  hCellRadius : ∀ i (g : G), g ∈ partition.cell i →
    dJ g (center i) ≤ radius
  hThetaLo : 0 ≤ lo
  meanSample : Pair → Fin partition.n → ℚ
  meanSampleError : Pair → ℝ
  hMeanSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ meanSampleError a
  hMeanSample : ∀ a ∈ c.s, ∀ i,
    |F e a (center i) - (meanSample a i : ℝ)| ≤ meanSampleError a
  secondSample : Pair → Fin partition.n → ℚ
  secondSampleError : Pair → ℝ
  hSecondSampleError_nonneg : ∀ a ∈ c.s, 0 ≤ secondSampleError a
  hSecondSample : ∀ a ∈ c.s, ∀ i,
    |(F e a (center i))^2 - (secondSample a i : ℝ)| ≤
      secondSampleError a
  coefficientSample : Pair → Fin 4 → Fin partition.n → ℚ
  coefficientSampleError : Pair → Fin 4 → ℝ
  hCoefficientSampleError_nonneg : ∀ a ∈ c.s, ∀ j,
    0 ≤ coefficientSampleError a j
  hCoefficientSample : ∀ a ∈ c.s, ∀ j i,
    |F e a (center i) * p4Q2PZ37ACK_fourModeCharacter j (center i) -
      (coefficientSample a j i : ℝ)| ≤ coefficientSampleError a j

/-- Discharge every original physical receiver obligation of AFL
with the actual transfer/kernel/Perron/BCF constants just proved. -/
def p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFL_originalReceiverOnlyCellSamples H e lo hi c where
  partition := d.partition
  center := d.center
  radius := d.radius
  hRadius := d.hRadius
  hCellRadius := d.hCellRadius
  hThetaLo := d.hThetaLo
  receiverEnvelope := fun _ => MFF e
  hReceiverEnvelope_nonneg := by
    intro a ha
    exact p4Q2PZ37AFM_originalFFEnvelope_nonneg H e
  hReceiverBound := by
    intro a ha g
    exact p4Q2PZ37AFM_originalFF_abs_le_trueBCFNorm H e a g
  receiverSlope := fun a => P a*LU
  hReceiverSlope_nonneg := by
    intro a ha
    exact p4Q2PZ37AFM_originalFFSlope_nonneg H a
  hReceiverSlope := by
    intro a ha g h
    exact p4Q2PZ37AFM_originalFF_unconditionalChordSlope H e a g h
  meanSample := d.meanSample
  meanSampleError := d.meanSampleError
  hMeanSampleError_nonneg := d.hMeanSampleError_nonneg
  hMeanSample := d.hMeanSample
  secondSample := d.secondSample
  secondSampleError := d.secondSampleError
  hSecondSampleError_nonneg := d.hSecondSampleError_nonneg
  hSecondSample := d.hSecondSample
  coefficientSample := d.coefficientSample
  coefficientSampleError := d.coefficientSampleError
  hCoefficientSampleError_nonneg := d.hCoefficientSampleError_nonneg
  hCoefficientSample := d.hCoefficientSample

/-- Full original AFK certificate with no assumed receiver or
character variation constants. -/
def p4Q2PZ37AFM_toOriginalChordalCellSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFK_originalChordalCellSamples H e lo hi c :=
  p4Q2PZ37AFL_toOriginalChordalCellSamples H e c
    (p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples H e c d)

/-- Original four-mode cell uncertainty with the true original FF
receiver envelope and the z-dependent Perron prefactor P_z. -/
theorem p4Q2PZ37AFM_coefficientOscillation_eq_physicalConstants
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c)
    (a : Pair) (j : Fin 4) :
    p4Q2PZ37AFK_coefficientOscillation H e c
      (p4Q2PZ37AFM_toOriginalChordalCellSamples H e c d) a j =
      (P a*LU+MFF e)*d.radius+d.coefficientSampleError a j := by
  simpa [p4Q2PZ37AFM_toOriginalChordalCellSamples,
    p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples] using
    (p4Q2PZ37AFL_canonicalCoefficientOscillation_eq H e c
      (p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples H e c d) a j)

/-- Same authentic finite normalized SU(2) Haar quadrature. -/
def p4Q2PZ37AFM_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFL_toOriginalReceiverQuadrature H e c
    (p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples H e c d)

/-- The true original coefficient and variance interval certificate,
with only verified rational samples/cell data remaining. -/
def p4Q2PZ37AFM_toOriginalCoefficientVarianceCertificate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFL_toOriginalCoefficientVarianceCertificate H e c
    (p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples H e c d)

def p4Q2PZ37AFM_originalNumericOnlyShellCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c) :
    Finset Pair :=
  p4Q2PZ37AFL_originalReceiverOnlyShellCenters H e c
    (p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples H e c d)

/-- An actually passing numerical-only certificate has the TWO
strict signs of the unchanged original Wilson/Perron residual gap. -/
theorem p4Q2PZ37AFM_originalNumericOnlyCenter_trueSigns
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFM_originalNumericOnlyCellSamples H e lo hi c)
    (a : Pair) (ha : a ∈ p4Q2PZ37AFM_originalNumericOnlyShellCenters H e c d) :
    c.etaLo < p4Q2PZ37AFB_originalResidualGap H e lo a ∧
      p4Q2PZ37AFB_originalResidualGap H e hi a < -c.etaHi :=
  p4Q2PZ37AFL_originalReceiverOnlyCenter_trueSigns H e c
    (p4Q2PZ37AFM_toOriginalReceiverOnlyCellSamples H e c d) a ha

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalTransferInvSq_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalJQReceiver_eq_scaledTransferSection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalTransferSection_abs_le_trueEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalTransferSectionEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalUnitSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalTransferSection_unitChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalTransferSection_unconditionalChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalTransferSectionSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalFF_eq_affineTransferSection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalFFEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalFF_abs_le_trueBCFNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalFF_unconditionalChordSlope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalFFSlope_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_coefficientOscillation_eq_physicalConstants
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFM_originalNumericOnlyCenter_trueSigns
