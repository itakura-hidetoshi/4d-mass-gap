import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalVerifiedRationalIntervalReceiverV5_PZ37AFV
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFW — original four-mode character intervals without external data

AFV accepts independently certified rational intervals for both the genuine
FF/Perron receiver at the original AFQ twenty-four SU(2) centers and the four
original quaternion-translated Wilson characters.

AFW discharges the SECOND input UNCONDITIONALLY. The pre-existing ACK Haar
four-mode character is an actual original SU(2) quantity, and the proven
pointwise four-square identity gives the global bounds -1 <= phi_j(g) <= 1.
Those *fixed rational endpoints* define a fully proof-carrying AFV interval.
Only true FF receiver intervals at the finite original boundary samples
remain inputs; all squared and character-product intervals follow from AFV.

The universal [-1,1] character enclosure is deliberately conservative.
It produces zero-centered four-mode product samples and does NOT certify
nonzero Fourier coefficients or strict physical shell crossings. It does
not claim exact character values at the original twenty-four centers, nor
produce numerical certificates for the true receiver/Perron/transfer.
No surrogate Haar, geometry, dynamics, or additional physical hypothesis.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter

local instance p4Q2PZ37AFW_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFW_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFW_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFW_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFW_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFW_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- A single original quaternionic Wilson character cannot account for
more than the total of four nonnegative squares, proven exactly one in ACK. -/
theorem p4Q2PZ37AFW_originalCharacter_sq_le_one (j : Fin 4) (g : G) :
    (phi j g) ^ 2 ≤ (1 : ℝ) := by
  have hsum := p4Q2PZ37ACK_fourModeCharacter_sum_sq g
  have hsingle :
      (phi j g) ^ 2 ≤ ∑ k : Fin 4, (phi k g) ^ 2 :=
    Finset.single_le_sum
      (fun k _ => sq_nonneg (phi k g)) (Finset.mem_univ j)
  rw [hsum] at hsingle
  exact hsingle

/-- Genuine, unconditional rational endpoints for ALL original
quaternion-translated Wilson characters and ALL SU(2) elements. -/
theorem p4Q2PZ37AFW_originalCharacter_unitBounds
    (j : Fin 4) (g : G) :
    (-1 : ℝ) ≤ phi j g ∧ phi j g ≤ 1 := by
  have hs := p4Q2PZ37AFW_originalCharacter_sq_le_one j g
  constructor
  · nlinarith only [hs, sq_nonneg (phi j g + 1)]
  · nlinarith only [hs, sq_nonneg (phi j g - 1)]

theorem p4Q2PZ37AFW_originalCharacter_abs_le_one
    (j : Fin 4) (g : G) :
    |phi j g| ≤ (1 : ℝ) := by
  exact abs_le.mpr (p4Q2PZ37AFW_originalCharacter_unitBounds j g)

/-- No separately measured or postulated character interval is needed:
these literal RATIONAL endpoints already follow from the original ACK. -/
def p4Q2PZ37AFW_originalCharacterVerifiedInterval
    (j : Fin 4) (g : G) :
    p4Q2PZ37AFV_verifiedInterval (phi j g) where
  lower := -1
  upper := 1
  hLower := by
    simpa using (p4Q2PZ37AFW_originalCharacter_unitBounds j g).1
  hUpper := by
    simpa using (p4Q2PZ37AFW_originalCharacter_unitBounds j g).2

/-- The resulting character sample is literally zero and its
proven error is one; it is conservative, not a true character evaluation. -/
theorem p4Q2PZ37AFW_characterBall_center_zero (j : Fin 4) (g : G) :
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFW_originalCharacterVerifiedInterval j g)).sample = 0 := by
  norm_num [p4Q2PZ37AFV_intervalToBall,
    p4Q2PZ37AFW_originalCharacterVerifiedInterval]

theorem p4Q2PZ37AFW_characterBall_error_one (j : Fin 4) (g : G) :
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFW_originalCharacterVerifiedInterval j g)).error = 1 := by
  norm_num [p4Q2PZ37AFV_intervalToBall,
    p4Q2PZ37AFW_originalCharacterVerifiedInterval]

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0

local instance p4Q2PZ37AFW_links : Fintype Link := Fintype.ofFinite _

/-- Only real FF/Perron/transfer receiver inclusions are still open
finite numerical obligations. All four-mode character inclusions are
derived from ACK, with no independent character-data requirement. -/
structure p4Q2PZ37AFW_originalReceiverIntervalsOnly
    (e : Link) (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  receiver : (a : Pair) → a ∈ c.s →
    (i : Fin (Fintype.card Grid)) →
      p4Q2PZ37AFV_verifiedInterval (F e a (gridCenter i))

/-- Typed forgetful/derived map to the unmodified AFV interval interface.
The character component is DISCHARGED by the original ACK square identity. -/
def p4Q2PZ37AFW_toAFVOriginalIntervals
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c where
  receiver := d.receiver
  character := fun j i =>
    p4Q2PZ37AFW_originalCharacterVerifiedInterval j (gridCenter i)

/-- From only certified ORIGINAL receiver intervals, obtain AFV's
verified 24-cell sample table and all derived second/product errors. -/
noncomputable def p4Q2PZ37AFW_toOriginalVerifiedSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c :=
  p4Q2PZ37AFV_toOriginalVerifiedSamples H e c
    (p4Q2PZ37AFW_toAFVOriginalIntervals H e c d)

/-- The SAME original Perron/transfer/FF physical quadrature with
true AFQ cells and AFT/AFU optimized Haar mass bounds. -/
noncomputable def p4Q2PZ37AFW_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFV_toOriginalReceiverQuadrature H e c hlo
    (p4Q2PZ37AFW_toAFVOriginalIntervals H e c d)

/-- Literal original AFM->AFJ->AFI coefficient-and-variance path.
No new operator, probability measure or receiver is introduced. -/
noncomputable def p4Q2PZ37AFW_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFV_toOriginalCoefficientVariance H e c hlo
    (p4Q2PZ37AFW_toAFVOriginalIntervals H e c d)

/-- Original 4-mode physical coefficient with the already-proven AFU
centered Haar error, requiring ONLY verified original receiver intervals. -/
theorem p4Q2PZ37AFW_originalCoefficient_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) (s : ℚ) :
    |p4Q2PZ37ACK_originalFourModeCoefficient H b0 hb0 e a j -
      (p4Q2PZ37AFJ_originalCoefficientCenter H e c
        (p4Q2PZ37AFW_toOriginalReceiverQuadrature H e c hlo d) a j : ℝ)| ≤
      (p4Q2PZ37AFW_toOriginalReceiverQuadrature H e c hlo d).coefficientOsc a j +
        p4Q2PZ37AFU_centeredHaarWeightError
          ((p4Q2PZ37AFW_toOriginalVerifiedSamples H e c d).coefficientSample a j) s := by
  exact p4Q2PZ37AFU_originalCoefficient_centeredAccuracy
    H e c hlo (p4Q2PZ37AFW_toOriginalVerifiedSamples H e c d) a ha j s

theorem p4Q2PZ37AFW_originalMean_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (s : ℚ) :
    |(∫ g : G, F e a g ∂normalizedCompactHaar G) -
      (p4Q2PZ37AFJ_originalMeanCenter H e c
        (p4Q2PZ37AFW_toOriginalReceiverQuadrature H e c hlo d) a : ℝ)| ≤
      (p4Q2PZ37AFW_toOriginalReceiverQuadrature H e c hlo d).meanOsc a +
        p4Q2PZ37AFU_centeredHaarWeightError
          ((p4Q2PZ37AFW_toOriginalVerifiedSamples H e c d).meanSample a) s := by
  exact p4Q2PZ37AFU_originalMean_centeredAccuracy
    H e c hlo (p4Q2PZ37AFW_toOriginalVerifiedSamples H e c d) a ha s

theorem p4Q2PZ37AFW_originalSecond_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (s : ℚ) :
    |(∫ g : G, (F e a g) ^ 2 ∂normalizedCompactHaar G) -
      (p4Q2PZ37AFJ_originalSecondCenter H e c
        (p4Q2PZ37AFW_toOriginalReceiverQuadrature H e c hlo d) a : ℝ)| ≤
      (p4Q2PZ37AFW_toOriginalReceiverQuadrature H e c hlo d).secondOsc a +
        p4Q2PZ37AFU_centeredHaarWeightError
          ((p4Q2PZ37AFW_toOriginalVerifiedSamples H e c d).secondSample a) s := by
  exact p4Q2PZ37AFU_originalSecond_centeredAccuracy
    H e c hlo (p4Q2PZ37AFW_toOriginalVerifiedSamples H e c d) a ha s

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFW_originalCharacter_sq_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFW_originalCharacter_unitBounds
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFW_originalCharacter_abs_le_one
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFW_originalCharacterVerifiedInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFW_characterBall_center_zero
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFW_characterBall_error_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_toAFVOriginalIntervals
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_toOriginalVerifiedSamples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_toOriginalReceiverQuadrature
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_toOriginalCoefficientVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_originalCoefficient_centeredAccuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_originalMean_centeredAccuracy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFW_originalSecond_centeredAccuracy
