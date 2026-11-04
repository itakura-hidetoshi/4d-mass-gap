import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalExact24CenterFourModeV5_PZ37AFX
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFY — original 24-center product error with zero character error

AFX proved the EXACT rational value q_j,i of each original quaternion-
translated Wilson character at all genuine AFQ 24 original SU(2) centers.
AFV's verified receiver intervals still enclose the ACTUAL original
Perron/transfer/FF physical receiver, not a surrogate numerical model.

AFY proves that the original center product F(a,g_i) * phi_j(g_i) has
the fixed rational center q_F(a,i) * q_j,i and an error of ONLY
|q_j,i| * epsilon_F(a,i), because epsilon_phi is literally ZERO.
This is a tightened, typed specialization of AFV's general ballMul.

The resulting exact per-center error and its 24-center sum are shown to
be the errors in the UNCHANGED AFX -> AFV -> AFT -> AFJ -> AFI original
receiver certificate. In particular the full product error sum is no
larger than the sum of the genuine receiver interval half-widths.

No independently evaluated concrete FF receiver/Perron/transfer rational
interval, physical two-sign shell, uniform coercivity, Hamiltonian gap,
or continuum 4D Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ComplexConjugate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter
local notation "qChar" => p4Q2PZ37AFX_exactRationalCharacter

local instance p4Q2PZ37AFY_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AFY_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AFY_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AFY_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AFY_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AFY_probability :
    IsProbabilityMeasure (normalizedCompactHaar G) :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Multiplication by an EXACT rational factor creates no additional
numerical uncertainty. The only input is a genuine verified ball for x. -/
theorem p4Q2PZ37AFY_exactRationalProduct_bound
    {x : ℝ} (bx : p4Q2PZ37AFV_certifiedBall x) (q : ℚ) :
    |x * (q : ℝ) - ((bx.sample * q : ℚ) : ℝ)| ≤
      |(q : ℝ)| * bx.error := by
  have hmul :
      x * (q : ℝ) - ((bx.sample * q : ℚ) : ℝ) =
        (x - (bx.sample : ℝ)) * (q : ℝ) := by
    push_cast
    ring
  rw [hmul, abs_mul]
  calc
    |x - (bx.sample : ℝ)| * |(q : ℝ)| ≤
        bx.error * |(q : ℝ)| :=
      mul_le_mul_of_nonneg_right bx.hContains (abs_nonneg _)
    _ = |(q : ℝ)| * bx.error := mul_comm _ _

/-- Fully proof-carrying ball for a receiver multiplied by an EXACT
rational character; its midpoint is rational and its error is explicit. -/
def p4Q2PZ37AFY_exactRationalProduct_ball
    {x : ℝ} (bx : p4Q2PZ37AFV_certifiedBall x) (q : ℚ) :
    p4Q2PZ37AFV_certifiedBall (x * (q : ℝ)) where
  sample := bx.sample * q
  error := |(q : ℝ)| * bx.error
  error_nonneg := mul_nonneg (abs_nonneg _) bx.error_nonneg
  hContains := p4Q2PZ37AFY_exactRationalProduct_bound bx q

/-- AFV general-product sample is the exact rational product when the
second certified sample is the exact rational character. -/
theorem p4Q2PZ37AFY_generalProduct_exactSample
    {x y : ℝ}
    (bx : p4Q2PZ37AFV_certifiedBall x)
    (byy : p4Q2PZ37AFV_certifiedBall y)
    (q : ℚ) (hq : byy.sample = q) :
    (p4Q2PZ37AFV_ballMul bx byy).sample = bx.sample * q := by
  change bx.sample * byy.sample = bx.sample * q
  rw [hq]

/-- With zero character error, the old AFV multiplication formula
reduces EXACTLY to |q| * receiverError, not merely to an upper bound. -/
theorem p4Q2PZ37AFY_generalProduct_zeroCharacterError
    {x y : ℝ}
    (bx : p4Q2PZ37AFV_certifiedBall x)
    (byy : p4Q2PZ37AFV_certifiedBall y)
    (q : ℚ) (hq : byy.sample = q) (hzero : byy.error = 0) :
    (p4Q2PZ37AFV_ballMul bx byy).error =
      |(q : ℝ)| * bx.error := by
  change
    bx.error * (|(byy.sample : ℝ)| + byy.error) +
      |(bx.sample : ℝ)| * byy.error = |(q : ℝ)| * bx.error
  rw [hq, hzero]
  ring

/-- The actual AFX singleton rational character ball has the literal
rational table entry as sample (not merely a real approximation). -/
theorem p4Q2PZ37AFY_originalCharacter_exactSample
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFX_originalCharacterSingleton j i)).sample =
        qChar j i := by
  change ((qChar j i + qChar j i) / 2 : ℚ) = qChar j i
  ring

/-- Each true 24-center rational Wilson character is bounded by 1
because it IS the original ACK four-mode character. -/
theorem p4Q2PZ37AFY_originalCharacter_exactAbs_le_one
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    |(qChar j i : ℝ)| ≤ (1 : ℝ) := by
  rw [← p4Q2PZ37AFX_originalCenter_character_exact]
  exact p4Q2PZ37AFW_originalCharacter_abs_le_one j (gridCenter i)

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

local instance p4Q2PZ37AFY_links : Fintype Link := Fintype.ofFinite _

/-- The actual original FF receiver times the actual Wilson character
at each actual AFQ center is enclosed with zero character uncertainty. -/
theorem p4Q2PZ37AFY_originalCenter_productBound
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    |F e a (gridCenter i) * phi j (gridCenter i) -
      (((p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).sample *
        qChar j i : ℚ) : ℝ)| ≤
      |(qChar j i : ℝ)| *
        (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error := by
  rw [p4Q2PZ37AFX_originalCenter_character_exact]
  exact p4Q2PZ37AFY_exactRationalProduct_bound
    (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)) (qChar j i)

/-- Explicit true-physical-coefficient pointwise ball, constructed from
ONLY the genuine receiver rational interval already required in AFX. -/
noncomputable def p4Q2PZ37AFY_originalCenter_productBall
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_certifiedBall
      (F e a (gridCenter i) * phi j (gridCenter i)) := by
  rw [p4Q2PZ37AFX_originalCenter_character_exact]
  exact p4Q2PZ37AFY_exactRationalProduct_ball
    (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)) (qChar j i)

/-- The UNMODIFIED AFV coefficient-ball has the exact AFY product
sample after inserting AFX's genuine zero-error character singleton. -/
theorem p4Q2PZ37AFY_originalAFV_coefficientSample_exact
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    (p4Q2PZ37AFV_coefficientBall H e c
      (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d) a ha j i).sample =
      (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).sample *
        qChar j i := by
  change
    (p4Q2PZ37AFV_ballMul
      (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i))
      (p4Q2PZ37AFV_intervalToBall
        (p4Q2PZ37AFX_originalCharacterSingleton j i))).sample =
      (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).sample * qChar j i
  exact p4Q2PZ37AFY_generalProduct_exactSample
    (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i))
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFX_originalCharacterSingleton j i))
    (qChar j i) (p4Q2PZ37AFY_originalCharacter_exactSample j i)

/-- The original AFV ball's ERROR, not merely an alternative bound,
is exactly the certified true receiver error times the rational table. -/
theorem p4Q2PZ37AFY_originalAFV_coefficientError_exact
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    (p4Q2PZ37AFV_coefficientBall H e c
      (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d) a ha j i).error =
      |(qChar j i : ℝ)| *
        (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error := by
  change
    (p4Q2PZ37AFV_ballMul
      (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i))
      (p4Q2PZ37AFV_intervalToBall
        (p4Q2PZ37AFX_originalCharacterSingleton j i))).error =
      |(qChar j i : ℝ)| *
        (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error
  exact p4Q2PZ37AFY_generalProduct_zeroCharacterError
    (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i))
    (p4Q2PZ37AFV_intervalToBall
      (p4Q2PZ37AFX_originalCharacterSingleton j i))
    (qChar j i)
    (p4Q2PZ37AFY_originalCharacter_exactSample j i)
    (p4Q2PZ37AFX_originalCharacterSingleton_zeroError j i)

/-- Direct typed link to AFT's original physical 24-cell table:
its rational coefficient samples are the literal FF rational midpoint
multiplied by the original exact AFX rational character table. -/
theorem p4Q2PZ37AFY_originalAFT_coefficientSample_exact
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s)
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    (p4Q2PZ37AFX_toOriginalVerifiedSamples H e c d).coefficientSample a j i =
      (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).sample * qChar j i := by
  change
    (if h : a ∈ c.s then
      (p4Q2PZ37AFV_coefficientBall H e c
        (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d) a h j i).sample
      else 0) =
      (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).sample * qChar j i
  simpa only [dif_pos ha] using
    (p4Q2PZ37AFY_originalAFV_coefficientSample_exact H e c d a ha j i)

/-- The AFT 24-cell physical coefficient error is EXACTLY the sum of
|actual rational Wilson character| times true FF receiver half-width.
No character-uncertainty or unstated numerical input remains. -/
theorem p4Q2PZ37AFY_originalAFT_coefficientError_exact
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) :
    (p4Q2PZ37AFX_toOriginalVerifiedSamples H e c d).coefficientSampleError a j =
      ∑ i : Fin (Fintype.card Grid),
        |(qChar j i : ℝ)| *
          (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error := by
  change
    (if h : a ∈ c.s then
      ∑ i : Fin (Fintype.card Grid),
        (p4Q2PZ37AFV_coefficientBall H e c
          (p4Q2PZ37AFX_toAFVOriginalIntervals H e c d) a h j i).error
      else 0) = _
  simp only [dif_pos ha]
  apply Finset.sum_congr rfl
  intro i _
  exact p4Q2PZ37AFY_originalAFV_coefficientError_exact H e c d a ha j i

/-- The original AFT four-mode sample-error budget is bounded by
the same original finite receiver half-width sum, with factor <= 1.
This loses NO physical assumptions and improves the AFW [-1,1] input. -/
theorem p4Q2PZ37AFY_originalAFT_error_le_receiverErrors
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) :
    (p4Q2PZ37AFX_toOriginalVerifiedSamples H e c d).coefficientSampleError a j ≤
      ∑ i : Fin (Fintype.card Grid),
        (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error := by
  rw [p4Q2PZ37AFY_originalAFT_coefficientError_exact H e c d a ha j]
  apply Finset.sum_le_sum
  intro i _
  calc
    |(qChar j i : ℝ)| *
        (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error ≤
      (1 : ℝ) * (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AFY_originalCharacter_exactAbs_le_one j i)
        (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error_nonneg
    _ = (p4Q2PZ37AFV_intervalToBall (d.receiver a ha i)).error := one_mul _

/-- The sharpened AFT table is passed to the unchanged AFU centered
genuine Haar quadrature bound for the ORIGINAL four-mode coefficient. -/
theorem p4Q2PZ37AFY_originalCoefficient_centeredAccuracy
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (d : p4Q2PZ37AFW_originalReceiverIntervalsOnly H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4) (s : ℚ) :
    |p4Q2PZ37ACK_originalFourModeCoefficient H b0 hb0 e a j -
      (p4Q2PZ37AFJ_originalCoefficientCenter H e c
        (p4Q2PZ37AFX_toOriginalReceiverQuadrature H e c hlo d) a j : ℝ)| ≤
      (p4Q2PZ37AFX_toOriginalReceiverQuadrature H e c hlo d).coefficientOsc a j +
        p4Q2PZ37AFU_centeredHaarWeightError
          ((p4Q2PZ37AFX_toOriginalVerifiedSamples H e c d).coefficientSample a j) s := by
  exact p4Q2PZ37AFU_originalCoefficient_centeredAccuracy
    H e c hlo (p4Q2PZ37AFX_toOriginalVerifiedSamples H e c d) a ha j s

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFY_exactRationalProduct_bound
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFY_exactRationalProduct_ball
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFY_generalProduct_exactSample
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFY_generalProduct_zeroCharacterError
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFY_originalCharacter_exactSample
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFY_originalCharacter_exactAbs_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalCenter_productBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalCenter_productBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalAFV_coefficientSample_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalAFV_coefficientError_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalAFT_coefficientSample_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalAFT_coefficientError_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalAFT_error_le_receiverErrors
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFY_originalCoefficient_centeredAccuracy
