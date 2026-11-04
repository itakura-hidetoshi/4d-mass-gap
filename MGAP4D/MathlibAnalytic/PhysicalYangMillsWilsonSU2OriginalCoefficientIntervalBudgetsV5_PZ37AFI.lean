import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalIntervalShellWitnessesV5_PZ37AFH
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFI — certified coefficient/variance error budgets for genuine intervals

AFH accepts sound intervals enclosing the TRUE Wilson/Perron four-mode
squared amplitude and higher-character Haar residual. AFI builds those
intervals directly from four original ACK Haar coefficients and the
original ACL Wilson/Perron receiver variance, using the EXACT ACM identities

  A(z)^2 = sum_{j : Fin 4} m_j(z)^2,
  V(z) = 4 * A(z)^2 + W(z).

A finite certificate supplies rational approximations of the four
TRUE coefficients and the TRUE variance, together with formally proved,
nonnegative errors at every point of the existing original AFG net.
A squared-coefficient error contributes

  delta_j * (2 * |q_j| + delta_j)

to the squared-amplitude error. Consequently the true original amplitude
square and residual lie in explicitly constructed rational-center
intervals with real, nonnegative error radii:

  aHat = sum_j q_j^2;                dA = sum_j delta_j(2|q_j|+delta_j)
  wHat = vHat - 4*aHat;              dW = deltaV + 4*dA
  aHat-dA <= A^2 <= aHat+dA;         wHat-dW <= W <= wHat+dW.

The same amplitude error is used in both W and A: it is NOT assumed
independent of the original physical residual. Exact sign budgets
for thresholds theta then take the form

  vHat - (4+theta)*aHat +/- (deltaV+(4+theta)*dA).

The certified finite rational data thus yield an actual AFH original
interval witness, authentic strict shell centers, original Haar ball
floors and AFH's disjoint packing continuation. No numerical rational
data or their rigorous errors are produced by this theorem. They must be
supplied and verified separately. No H-uniform coercivity or continuum
Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "mu" => normalizedCompactHaar G
local instance p4Q2PZ37AFI_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFI_compactG : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFI_countableG : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFI_measurableG : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFI_borelG : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFI_probabilityG : IsProbabilityMeasure mu :=
  normalizedCompactHaar_isProbabilityMeasure G

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "outer" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H 2
local notation "D" => p4Q2PZ37ADL_originalFullBoundaryChordalDistance H
local notation "Shell" => p4Q2PZ37AFF_originalExceptionalShell H
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "m" => p4Q2PZ37ACK_originalFourModeCoefficient H
local notation "V" => p4Q2PZ37ACL_originalCenteredReceiverVariance H
local notation "A" => p4Q2PZ37ACM_originalCovarianceAmplitude H
local notation "W" => p4Q2PZ37ACK_originalFourModeResidualEnergy H
local notation "Gap" => p4Q2PZ37AFB_originalResidualGap H

local instance p4Q2PZ37AFI_links : Fintype Link := Fintype.ofFinite _
local instance p4Q2PZ37AFI_outerProbability : IsProbabilityMeasure outer := by
  unfold periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure
    periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure
  infer_instance

/-- Finite rational numerical candidates with proofs that they enclose
the TRUE four ACK coefficients and the TRUE ACL receiver variance.
Errors are stated at the actual original AFG finite boundary-pair net.
This structure does not invent or assert any evaluated samples. -/
structure p4Q2PZ37AFI_originalCoefficientVarianceCertificate
    (H : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  coefficientCenter :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
        Fin 4 → ℚ
  coefficientError :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) →
        Fin 4 → ℝ
  varianceCenter :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℚ
  varianceError :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2) → ℝ
  hThetaLo : 0 ≤ lo
  hCoefficientError_nonneg : ∀ a ∈ c.s, ∀ j, 0 ≤ coefficientError a j
  hVarianceError_nonneg : ∀ a ∈ c.s, 0 ≤ varianceError a
  hCoefficientAccuracy : ∀ a ∈ c.s, ∀ j,
    |p4Q2PZ37ACK_originalFourModeCoefficient H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le e a j -
        (coefficientCenter a j : ℝ)| ≤ coefficientError a j
  hVarianceAccuracy : ∀ a ∈ c.s,
    |p4Q2PZ37ACL_originalCenteredReceiverVariance H
      p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le e a -
        (varianceCenter a : ℝ)| ≤ varianceError a

/-- Center of the true squared four-mode amplitude, obtained from
FOUR rational approximations to the original Haar coefficients. -/
def p4Q2PZ37AFI_originalAmplitudeSquareEstimate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) : ℝ :=
  ∑ j : Fin 4, (d.coefficientCenter a j : ℝ)^2

/-- Explicit sum of four certified squared-coefficient error budgets. -/
def p4Q2PZ37AFI_originalAmplitudeSquareError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) : ℝ :=
  ∑ j : Fin 4, d.coefficientError a j *
    (2 * |(d.coefficientCenter a j : ℝ)| + d.coefficientError a j)

/-- The true residual is reconstructed from the SAME original receiver
variance and the SAME squared four-mode amplitude estimate. -/
def p4Q2PZ37AFI_originalResidualEstimate
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) : ℝ :=
  (d.varianceCenter a : ℝ) -
    4 * p4Q2PZ37AFI_originalAmplitudeSquareEstimate H e c d a

/-- Correlated true residual error, not a second independent W sample. -/
def p4Q2PZ37AFI_originalResidualError
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) : ℝ :=
  d.varianceError a +
    4 * p4Q2PZ37AFI_originalAmplitudeSquareError H e c d a

local notation "aHat" => p4Q2PZ37AFI_originalAmplitudeSquareEstimate H
local notation "dA" => p4Q2PZ37AFI_originalAmplitudeSquareError H
local notation "wHat" => p4Q2PZ37AFI_originalResidualEstimate H
local notation "dW" => p4Q2PZ37AFI_originalResidualError H

/-- Elementary enclosure lemma: accuracy for x itself gives an
EXPLICIT rigorous error bound for the square. -/
private theorem p4Q2PZ37AFI_squareError
    (x y delta : ℝ) (hNonneg : 0 ≤ delta)
    (hApprox : |x - y| ≤ delta) :
    |x^2 - y^2| ≤ delta * (2 * |y| + delta) := by
  have hPlus : |x + y| ≤ 2 * |y| + delta := by
    calc
      |x + y| = |(x - y) + (y + y)| := by congr 1 <;> ring
      _ ≤ |x - y| + |y + y| := abs_add_le _ _
      _ ≤ delta + (|y| + |y|) :=
        add_le_add hApprox (abs_add_le _ _)
      _ = 2 * |y| + delta := by ring
  calc
    |x^2 - y^2| = |x - y| * |x + y| := by
      rw [show x^2 - y^2 = (x-y)*(x+y) by ring, abs_mul]
    _ ≤ delta * |x + y| :=
      mul_le_mul_of_nonneg_right hApprox (abs_nonneg _)
    _ ≤ delta * (2 * |y| + delta) :=
      mul_le_mul_of_nonneg_left hPlus hNonneg

/-- Every original Haar coefficient contributes its certified
squared-value enclosure; no functional or Haar approximation is hidden. -/
theorem p4Q2PZ37AFI_originalCoefficientSquare_error
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) :
    |(m b0 hb0 e a j)^2 - (d.coefficientCenter a j : ℝ)^2| ≤
      d.coefficientError a j *
        (2 * |(d.coefficientCenter a j : ℝ)| + d.coefficientError a j) :=
  p4Q2PZ37AFI_squareError
    (m b0 hb0 e a j) (d.coefficientCenter a j : ℝ)
    (d.coefficientError a j)
    (d.hCoefficientError_nonneg a ha j)
    (d.hCoefficientAccuracy a ha j)

/-- Finite sums of nonnegative coefficient budgets remain nonnegative. -/
theorem p4Q2PZ37AFI_amplitudeSquareError_nonneg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤ dA e c d a := by
  unfold p4Q2PZ37AFI_originalAmplitudeSquareError
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (d.hCoefficientError_nonneg a ha j)
    (add_nonneg (mul_nonneg (by norm_num) (abs_nonneg _))
      (d.hCoefficientError_nonneg a ha j))

/-- BOTH sides of the ORIGINAL squared-amplitude interval follow from
the exact ACM finite Haar coefficient identity and four sample errors. -/
theorem p4Q2PZ37AFI_originalAmplitudeSquare_bounds
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    aHat e c d a - dA e c d a ≤ (A b0 hb0 e a)^2 ∧
      (A b0 hb0 e a)^2 ≤ aHat e c d a + dA e c d a := by
  have hTerm (j : Fin 4) :=
    p4Q2PZ37AFI_originalCoefficientSquare_error H e c d a ha j
  have hLo (j : Fin 4) :
      (d.coefficientCenter a j : ℝ)^2 -
        d.coefficientError a j *
          (2 * |(d.coefficientCenter a j : ℝ)| + d.coefficientError a j) ≤
        (m b0 hb0 e a j)^2 := by
    have h := (abs_le.mp (hTerm j)).1
    linarith only [h]
  have hHi (j : Fin 4) :
      (m b0 hb0 e a j)^2 ≤
        (d.coefficientCenter a j : ℝ)^2 +
          d.coefficientError a j *
            (2 * |(d.coefficientCenter a j : ℝ)| + d.coefficientError a j) := by
    have h := (abs_le.mp (hTerm j)).2
    linarith only [h]
  have hSumLo : (∑ j : Fin 4,
      (d.coefficientCenter a j : ℝ)^2 -
        d.coefficientError a j *
          (2 * |(d.coefficientCenter a j : ℝ)| + d.coefficientError a j)) ≤
          ∑ j : Fin 4, (m b0 hb0 e a j)^2 :=
    Finset.sum_le_sum (fun j _ => hLo j)
  have hSumHi : (∑ j : Fin 4, (m b0 hb0 e a j)^2) ≤
      ∑ j : Fin 4,
        (d.coefficientCenter a j : ℝ)^2 +
          d.coefficientError a j *
            (2 * |(d.coefficientCenter a j : ℝ)| + d.coefficientError a j) :=
    Finset.sum_le_sum (fun j _ => hHi j)
  constructor
  · rw [p4Q2PZ37ACM_originalCovarianceAmplitude_sq H b0 hb0 e a]
    simpa only [p4Q2PZ37AFI_originalAmplitudeSquareEstimate,
      p4Q2PZ37AFI_originalAmplitudeSquareError,
      Finset.sum_sub_distrib] using hSumLo
  · rw [p4Q2PZ37ACM_originalCovarianceAmplitude_sq H b0 hb0 e a]
    simpa only [p4Q2PZ37AFI_originalAmplitudeSquareEstimate,
      p4Q2PZ37AFI_originalAmplitudeSquareError,
      Finset.sum_add_distrib] using hSumHi

/-- The explicit correlated W error is nonnegative at every certified
original full-boundary sample. -/
theorem p4Q2PZ37AFI_residualError_nonneg
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤ dW e c d a := by
  unfold p4Q2PZ37AFI_originalResidualError
  exact add_nonneg (d.hVarianceError_nonneg a ha)
    (mul_nonneg (by norm_num)
      (p4Q2PZ37AFI_amplitudeSquareError_nonneg H e c d a ha))

/-- Original ACL variance and exact ACM allocation certify BOTH sides
of the higher-character residual, without a separate W oracle. -/
theorem p4Q2PZ37AFI_originalResidual_bounds
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    wHat e c d a - dW e c d a ≤ W b0 hb0 e a ∧
      W b0 hb0 e a ≤ wHat e c d a + dW e c d a := by
  have hVar := abs_le.mp (d.hVarianceAccuracy a ha)
  have hAmp := p4Q2PZ37AFI_originalAmplitudeSquare_bounds H e c d a ha
  have hIdentity :=
    p4Q2PZ37ACM_originalVariance_eq_amplitude_residual H b0 hb0 e a
  change V b0 hb0 e a = 4 * (A b0 hb0 e a)^2 + W b0 hb0 e a
    at hIdentity
  dsimp only [p4Q2PZ37AFI_originalResidualEstimate,
    p4Q2PZ37AFI_originalResidualError]
  constructor
  · linarith only [hVar.1, hAmp.2, hIdentity]
  · linarith only [hVar.2, hAmp.1, hIdentity]

/-- The requested AFH interval evidence is CONSTRUCTED from the four
actual ACK modes plus original receiver variance and certified errors. -/
def p4Q2PZ37AFI_derivedOriginalIntervalEvidence
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c) :
    p4Q2PZ37AFH_originalIntervalEvidence H e lo hi c where
  amplitudeLower := fun a => aHat e c d a - dA e c d a
  amplitudeUpper := fun a => aHat e c d a + dA e c d a
  residualLower := fun a => wHat e c d a - dW e c d a
  residualUpper := fun a => wHat e c d a + dW e c d a
  hThetaLo := d.hThetaLo
  hAmplitudeLower := by
    intro a ha
    exact (p4Q2PZ37AFI_originalAmplitudeSquare_bounds H e c d a ha).1
  hAmplitudeUpper := by
    intro a ha
    exact (p4Q2PZ37AFI_originalAmplitudeSquare_bounds H e c d a ha).2
  hResidualLower := by
    intro a ha
    exact (p4Q2PZ37AFI_originalResidual_bounds H e c d a ha).1
  hResidualUpper := by
    intro a ha
    exact (p4Q2PZ37AFI_originalResidual_bounds H e c d a ha).2

/-- Fully certified finite interval shell-center filter for the actual
original SU(2) boundary pair metric and Haar measure. -/
def p4Q2PZ37AFI_derivedOriginalShellCenters
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c) :
    Finset Pair :=
  p4Q2PZ37AFH_originalIntervalRobustCenters H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d)

/-- The two interval widths are exactly twice the nonnegative
computed errors; an explicit quantitative accuracy budget. -/
theorem p4Q2PZ37AFI_amplitudeInterval_width
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤
      (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).amplitudeUpper a -
      (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).amplitudeLower a ∧
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).amplitudeUpper a -
      (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).amplitudeLower a =
        2 * dA e c d a := by
  dsimp only [p4Q2PZ37AFI_derivedOriginalIntervalEvidence]
  constructor
  · have h := p4Q2PZ37AFI_amplitudeSquareError_nonneg H e c d a ha
    linarith only [h]
  · ring

/-- The higher-character residual width is exactly twice
(deltaVariance + 4*deltaAmplitudeSquared). -/
theorem p4Q2PZ37AFI_residualInterval_width
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) :
    0 ≤
      (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).residualUpper a -
      (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).residualLower a ∧
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).residualUpper a -
      (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d).residualLower a =
        2 * dW e c d a := by
  dsimp only [p4Q2PZ37AFI_derivedOriginalIntervalEvidence]
  constructor
  · have h := p4Q2PZ37AFI_residualError_nonneg H e c d a ha
    linarith only [h]
  · ring

/-- A sufficient, directly checkable pair of finite rational-center
and rigorous-error margin tests. The coefficient (4+theta) is fixed by
the TRUE ACM variance allocation, not a substituted receiver. -/
theorem p4Q2PZ37AFI_numericMargins_select_trueShellCenter
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (hLo : c.etaLo <
      (d.varianceCenter a : ℝ) - (4 + lo) * aHat e c d a -
        (d.varianceError a + (4 + lo) * dA e c d a))
    (hHi :
      (d.varianceCenter a : ℝ) - (4 + hi) * aHat e c d a +
        (d.varianceError a + (4 + hi) * dA e c d a) < -c.etaHi) :
    a ∈ p4Q2PZ37AFI_derivedOriginalShellCenters H e c d := by
  change a ∈ p4Q2PZ37AFH_originalIntervalRobustCenters H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d)
  rw [p4Q2PZ37AFH_originalIntervalRobustCenters]
  refine Finset.mem_filter.mpr ⟨ha, ?_⟩
  constructor
  · change c.etaLo <
      (wHat e c d a - dW e c d a) -
        lo * (aHat e c d a + dA e c d a)
    have hEq :
      (wHat e c d a - dW e c d a) -
        lo * (aHat e c d a + dA e c d a) =
      (d.varianceCenter a : ℝ) - (4 + lo) * aHat e c d a -
        (d.varianceError a + (4 + lo) * dA e c d a) := by
      simp only [p4Q2PZ37AFI_originalResidualEstimate,
        p4Q2PZ37AFI_originalResidualError]
      ring
    rw [hEq]
    exact hLo
  · change (wHat e c d a + dW e c d a) -
      hi * (aHat e c d a - dA e c d a) < -c.etaHi
    have hEq :
      (wHat e c d a + dW e c d a) -
        hi * (aHat e c d a - dA e c d a) =
      (d.varianceCenter a : ℝ) - (4 + hi) * aHat e c d a +
        (d.varianceError a + (4 + hi) * dA e c d a) := by
      simp only [p4Q2PZ37AFI_originalResidualEstimate,
        p4Q2PZ37AFI_originalResidualError]
      ring
    rw [hEq]
    exact hHi

/-- The computed finite test has no false-positive center: every such
center has the two ACTUAL original Wilson/Perron strict signs. -/
theorem p4Q2PZ37AFI_derivedCenter_trueOriginalSigns
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair)
    (ha : a ∈ p4Q2PZ37AFI_derivedOriginalShellCenters H e c d) :
    c.etaLo < Gap e lo a ∧ Gap e hi a < -c.etaHi :=
  p4Q2PZ37AFH_intervalCenter_trueSigns H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d) a ha

/-- A passing finite rational/error check proves a positive,
unchanged original pair-Haar shell mass, not just a proxy shell. -/
theorem p4Q2PZ37AFI_numericMargins_give_positiveTrueHaarShell
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (hLo : c.etaLo <
      (d.varianceCenter a : ℝ) - (4 + lo) * aHat e c d a -
        (d.varianceError a + (4 + lo) * dA e c d a))
    (hHi :
      (d.varianceCenter a : ℝ) - (4 + hi) * aHat e c d a +
        (d.varianceError a + (4 + hi) * dA e c d a) < -c.etaHi) :
    0 < Measure.real outer (Shell e lo hi) := by
  have hCenter := p4Q2PZ37AFI_numericMargins_select_trueShellCenter
    H e c d a ha hLo hHi
  have hFloor := p4Q2PZ37AFH_intervalCenter_floor_le_shellMass
    H e c (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d) a hCenter
  exact (p4Q2PZ37AEA_explicitFloor_pos H c.r c.hR).trans_le hFloor

/-- The same certified finite candidate table supports the original
AFD 2r-greedy packing and positive genuine AEA Haar mass floor. -/
theorem p4Q2PZ37AFI_derivedOriginalPacking_exists
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c) :
    ∃ t : Finset Pair,
      t ⊆ p4Q2PZ37AFI_derivedOriginalShellCenters H e c d ∧
      (∀ a ∈ t, ∀ b ∈ t, a ≠ b → 2 * c.r ≤ D a b) ∧
      (∀ a ∈ p4Q2PZ37AFI_derivedOriginalShellCenters H e c d,
        ∃ b ∈ t, D a b < 2 * c.r) ∧
      (t.card : ℝ) * p4Q2PZ37AFD_originalHaarBallFloor H c.r ≤
        Measure.real outer (Shell e lo hi) :=
  p4Q2PZ37AFH_intervalPacking_exists H e c
    (p4Q2PZ37AFI_derivedOriginalIntervalEvidence H e c d)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_originalCoefficientSquare_error
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_amplitudeSquareError_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_originalAmplitudeSquare_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_residualError_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_originalResidual_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_amplitudeInterval_width
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_residualInterval_width
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_numericMargins_select_trueShellCenter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_derivedCenter_trueOriginalSigns
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_numericMargins_give_positiveTrueHaarShell
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFI_derivedOriginalPacking_exists
