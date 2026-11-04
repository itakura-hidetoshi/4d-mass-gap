import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCenteredHaarMassErrorV5_PZ37AFU
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AFV — proof-carrying rational intervals for the original FF receiver

AFU provides a noncomputable dense-rational choice for genuine SU(2)
receiver-center values. AFV separates independently supplied RATIONAL
endpoints from their Lean proof of inclusion of the TRUE real receiver
value. Interval centers are literal rational midpoint computations.
Sound finite interval arithmetic derives square and product certificates.

Only one receiver interval per genuine AFQ 24-center for each member
of the original finite boundary sample set, and four original Wilson
character intervals per center, are necessary. Squared receiver and
four-mode products are derived, not postulated as additional physical
numerical observations. The resultant AFT physical sample certificate
passes unchanged through the original AFM -> AFJ -> AFI pipeline.

This is a proof-checkable interface for externally verified numerical
intervals, NOT an assertion that those intervals have been evaluated.
No new Haar law, lattice model, boundary source, or gap hypothesis.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A rational numerical center with an independently proven real enclosure. -/
structure p4Q2PZ37AFV_certifiedBall (x : ℝ) where
  sample : ℚ
  error : ℝ
  error_nonneg : 0 ≤ error
  hContains : |x - (sample : ℝ)| ≤ error

/-- A REAL value sandwiched by explicit rational endpoints. The two
inequality proofs are the numerical verification obligations. -/
structure p4Q2PZ37AFV_verifiedInterval (x : ℝ) where
  lower : ℚ
  upper : ℚ
  hLower : (lower : ℝ) ≤ x
  hUpper : x ≤ (upper : ℝ)

theorem p4Q2PZ37AFV_interval_ordered {x : ℝ}
    (v : p4Q2PZ37AFV_verifiedInterval x) :
    v.lower ≤ v.upper := by
  exact_mod_cast (le_trans v.hLower v.hUpper)

/-- Rational midpoint and half-width are computed from the actual
rational endpoints, with no Classical choice for the midpoint. -/
def p4Q2PZ37AFV_intervalToBall {x : ℝ}
    (v : p4Q2PZ37AFV_verifiedInterval x) :
    p4Q2PZ37AFV_certifiedBall x where
  sample := (v.lower + v.upper) / 2
  error := (((v.upper - v.lower : ℚ) : ℝ) / 2)
  error_nonneg := by
    have h : (v.lower : ℝ) ≤ (v.upper : ℝ) :=
      le_trans v.hLower v.hUpper
    have hc : (((v.upper - v.lower : ℚ) : ℝ) / 2) =
        ((v.upper : ℝ) - (v.lower : ℝ)) / 2 := by
      push_cast
      ring
    rw [hc]
    linarith only [h]
  hContains := by
    have hm : ((((v.lower + v.upper) / 2 : ℚ) : ℝ)) =
        ((v.lower : ℝ) + (v.upper : ℝ)) / 2 := by
      push_cast
      ring
    have hr : (((v.upper - v.lower : ℚ) : ℝ) / 2) =
        ((v.upper : ℝ) - (v.lower : ℝ)) / 2 := by
      push_cast
      ring
    change |x - ((((v.lower + v.upper) / 2 : ℚ) : ℝ))| ≤
      (((v.upper - v.lower : ℚ) : ℝ) / 2)
    rw [hm, hr]
    apply abs_le.mpr
    constructor <;> linarith only [v.hLower, v.hUpper]

/-- A strictly positive rational LOWER endpoint verifies positivity
of the actual original real observable, without a heuristic sample. -/
theorem p4Q2PZ37AFV_interval_positive {x : ℝ}
    (v : p4Q2PZ37AFV_verifiedInterval x)
    (h : 0 < v.lower) : 0 < x := by
  have hR : (0 : ℝ) < (v.lower : ℝ) := by exact_mod_cast h
  exact lt_of_lt_of_le hR v.hLower

theorem p4Q2PZ37AFV_interval_negative {x : ℝ}
    (v : p4Q2PZ37AFV_verifiedInterval x)
    (h : v.upper < 0) : x < 0 := by
  have hR : (v.upper : ℝ) < 0 := by exact_mod_cast h
  exact lt_of_le_of_lt v.hUpper hR

/-- Square interval arithmetic: only the receiver center and radius
are needed to certify the exact original second observable. -/
def p4Q2PZ37AFV_ballSquare {x : ℝ}
    (b : p4Q2PZ37AFV_certifiedBall x) :
    p4Q2PZ37AFV_certifiedBall (x ^ 2) where
  sample := b.sample ^ 2
  error := b.error * (2 * |(b.sample : ℝ)| + b.error)
  error_nonneg := by
    apply mul_nonneg b.error_nonneg
    have h : 0 ≤ |(b.sample : ℝ)| := abs_nonneg _
    linarith only [h, b.error_nonneg]
  hContains := by
    have hs : |x + (b.sample : ℝ)| ≤
        b.error + 2 * |(b.sample : ℝ)| := by
      calc
        |x + (b.sample : ℝ)| =
            |(x - (b.sample : ℝ)) + 2 * (b.sample : ℝ)| := by
              congr 1
              ring
        _ ≤ |x - (b.sample : ℝ)| + |2 * (b.sample : ℝ)| := abs_add_le _ _
        _ = |x - (b.sample : ℝ)| + 2 * |(b.sample : ℝ)| := by
              rw [abs_mul]
              norm_num
        _ ≤ b.error + 2 * |(b.sample : ℝ)| := by
              linarith only [b.hContains]
    change |x ^ 2 - ((b.sample ^ 2 : ℚ) : ℝ)| ≤
      b.error * (2 * |(b.sample : ℝ)| + b.error)
    calc
      |x ^ 2 - ((b.sample ^ 2 : ℚ) : ℝ)| =
          |x - (b.sample : ℝ)| * |x + (b.sample : ℝ)| := by
            rw [show ((b.sample ^ 2 : ℚ) : ℝ) =
                (b.sample : ℝ) ^ 2 by norm_cast]
            rw [show x ^ 2 - (b.sample : ℝ) ^ 2 =
                (x - (b.sample : ℝ)) * (x + (b.sample : ℝ)) by ring, abs_mul]
      _ ≤ b.error * |x + (b.sample : ℝ)| :=
        mul_le_mul_of_nonneg_right b.hContains (abs_nonneg _)
      _ ≤ b.error * (b.error + 2 * |(b.sample : ℝ)|) :=
        mul_le_mul_of_nonneg_left hs b.error_nonneg
      _ = b.error * (2 * |(b.sample : ℝ)| + b.error) := by ring

/-- Product enclosure, with the exact receiver-times-Wilson-character
as target and rational product as center. -/
def p4Q2PZ37AFV_ballMul {x y : ℝ}
    (bx : p4Q2PZ37AFV_certifiedBall x)
    (byy : p4Q2PZ37AFV_certifiedBall y) :
    p4Q2PZ37AFV_certifiedBall (x * y) where
  sample := bx.sample * byy.sample
  error := bx.error * (|(byy.sample : ℝ)| + byy.error) +
    |(bx.sample : ℝ)| * byy.error
  error_nonneg := by
    apply add_nonneg
    · exact mul_nonneg bx.error_nonneg
        (add_nonneg (abs_nonneg _) byy.error_nonneg)
    · exact mul_nonneg (abs_nonneg _) byy.error_nonneg
  hContains := by
    have hy : |y| ≤ |(byy.sample : ℝ)| + byy.error := by
      calc
        |y| = |(y - (byy.sample : ℝ)) + (byy.sample : ℝ)| := by
          congr 1
          ring
        _ ≤ |y - (byy.sample : ℝ)| + |(byy.sample : ℝ)| := abs_add_le _ _
        _ ≤ |(byy.sample : ℝ)| + byy.error := by
          linarith only [byy.hContains]
    have hFirst :
        |x - (bx.sample : ℝ)| * |y| ≤
          bx.error * (|(byy.sample : ℝ)| + byy.error) := by
      calc
        _ ≤ bx.error * |y| :=
          mul_le_mul_of_nonneg_right bx.hContains (abs_nonneg _)
        _ ≤ bx.error * (|(byy.sample : ℝ)| + byy.error) :=
          mul_le_mul_of_nonneg_left hy bx.error_nonneg
    have hSecond :
        |(bx.sample : ℝ)| * |y - (byy.sample : ℝ)| ≤
          |(bx.sample : ℝ)| * byy.error :=
      mul_le_mul_of_nonneg_left byy.hContains (abs_nonneg _)
    change |x * y - ((bx.sample * byy.sample : ℚ) : ℝ)| ≤
      bx.error * (|(byy.sample : ℝ)| + byy.error) +
      |(bx.sample : ℝ)| * byy.error
    calc
      |x * y - ((bx.sample * byy.sample : ℚ) : ℝ)| =
          |(x - (bx.sample : ℝ)) * y +
              (bx.sample : ℝ) * (y - (byy.sample : ℝ))| := by
                rw [show ((bx.sample * byy.sample : ℚ) : ℝ) =
                    (bx.sample : ℝ) * (byy.sample : ℝ) by norm_cast]
                congr 1
                ring
      _ ≤ |(x - (bx.sample : ℝ)) * y| +
          |(bx.sample : ℝ) * (y - (byy.sample : ℝ))| :=
        abs_add_le _ _
      _ = |x - (bx.sample : ℝ)| * |y| +
          |(bx.sample : ℝ)| * |y - (byy.sample : ℝ)| := by
            rw [abs_mul, abs_mul]
      _ ≤ bx.error * (|(byy.sample : ℝ)| + byy.error) +
          |(bx.sample : ℝ)| * byy.error :=
        add_le_add hFirst hSecond

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Pair" => Cfg × Cfg
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "gridCenter" => p4Q2PZ37AFQ_originalCenters
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "hb0" => p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "F" => p4Q2PZ37ABZ_originalReceiverSection H b0 hb0 f0
local notation "phi" => p4Q2PZ37ACK_fourModeCharacter

local instance p4Q2PZ37AFV_links : Fintype Link := Fintype.ofFinite _

/-- Only finite true boundary sample points require receiver interval
verification. Wilson character interval verification is independent of
the boundary and reused at all boundary points. -/
structure p4Q2PZ37AFV_originalFiniteIntervalInput
    (e : Link) (lo hi : ℝ)
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi) where
  receiver : (a : Pair) → a ∈ c.s →
    (i : Fin (Fintype.card Grid)) →
      p4Q2PZ37AFV_verifiedInterval (F e a (gridCenter i))
  character : (j : Fin 4) →
    (i : Fin (Fintype.card Grid)) →
      p4Q2PZ37AFV_verifiedInterval (phi j (gridCenter i))

def p4Q2PZ37AFV_receiverBall
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_certifiedBall (F e a (gridCenter i)) :=
  p4Q2PZ37AFV_intervalToBall (t.receiver a ha i)

def p4Q2PZ37AFV_characterBall
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c)
    (j : Fin 4) (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_certifiedBall (phi j (gridCenter i)) :=
  p4Q2PZ37AFV_intervalToBall (t.character j i)

def p4Q2PZ37AFV_secondBall
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_certifiedBall ((F e a (gridCenter i)) ^ 2) :=
  p4Q2PZ37AFV_ballSquare
    (p4Q2PZ37AFV_receiverBall H e c t a ha i)

def p4Q2PZ37AFV_coefficientBall
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (j : Fin 4)
    (i : Fin (Fintype.card Grid)) :
    p4Q2PZ37AFV_certifiedBall
      (F e a (gridCenter i) * phi j (gridCenter i)) :=
  p4Q2PZ37AFV_ballMul
    (p4Q2PZ37AFV_receiverBall H e c t a ha i)
    (p4Q2PZ37AFV_characterBall H e c t j i)

/-- The original AFT 24-center certificate built from *only* true
receiver and original character rational intervals. Each sum of
nonnegative rational-halfwidth-derived errors controls each center. -/
noncomputable def p4Q2PZ37AFV_toOriginalVerifiedSamples
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c) :
    p4Q2PZ37AFT_original24CellVerifiedSamples H e lo hi c where
  meanSample := fun a i =>
    if ha : a ∈ c.s then
      (p4Q2PZ37AFV_receiverBall H e c t a ha i).sample else 0
  meanSampleError := fun a =>
    if ha : a ∈ c.s then
      ∑ i : Fin (Fintype.card Grid),
        (p4Q2PZ37AFV_receiverBall H e c t a ha i).error else 0
  hMeanSampleError_nonneg := by
    intro a ha
    simp only [dif_pos ha]
    exact Finset.sum_nonneg (fun i _ =>
      (p4Q2PZ37AFV_receiverBall H e c t a ha i).error_nonneg)
  hMeanSample := by
    intro a ha i
    simp only [dif_pos ha]
    exact le_trans
      (p4Q2PZ37AFV_receiverBall H e c t a ha i).hContains
      (Finset.single_le_sum
        (fun j _ => (p4Q2PZ37AFV_receiverBall H e c t a ha j).error_nonneg)
        (Finset.mem_univ i))
  secondSample := fun a i =>
    if ha : a ∈ c.s then
      (p4Q2PZ37AFV_secondBall H e c t a ha i).sample else 0
  secondSampleError := fun a =>
    if ha : a ∈ c.s then
      ∑ i : Fin (Fintype.card Grid),
        (p4Q2PZ37AFV_secondBall H e c t a ha i).error else 0
  hSecondSampleError_nonneg := by
    intro a ha
    simp only [dif_pos ha]
    exact Finset.sum_nonneg (fun i _ =>
      (p4Q2PZ37AFV_secondBall H e c t a ha i).error_nonneg)
  hSecondSample := by
    intro a ha i
    simp only [dif_pos ha]
    exact le_trans
      (p4Q2PZ37AFV_secondBall H e c t a ha i).hContains
      (Finset.single_le_sum
        (fun j _ => (p4Q2PZ37AFV_secondBall H e c t a ha j).error_nonneg)
        (Finset.mem_univ i))
  coefficientSample := fun a j i =>
    if ha : a ∈ c.s then
      (p4Q2PZ37AFV_coefficientBall H e c t a ha j i).sample else 0
  coefficientSampleError := fun a j =>
    if ha : a ∈ c.s then
      ∑ i : Fin (Fintype.card Grid),
        (p4Q2PZ37AFV_coefficientBall H e c t a ha j i).error else 0
  hCoefficientSampleError_nonneg := by
    intro a ha j
    simp only [dif_pos ha]
    exact Finset.sum_nonneg (fun i _ =>
      (p4Q2PZ37AFV_coefficientBall H e c t a ha j i).error_nonneg)
  hCoefficientSample := by
    intro a ha j i
    simp only [dif_pos ha]
    exact le_trans
      (p4Q2PZ37AFV_coefficientBall H e c t a ha j i).hContains
      (Finset.single_le_sum
        (fun k _ => (p4Q2PZ37AFV_coefficientBall H e c t a ha j k).error_nonneg)
        (Finset.mem_univ i))

/-- Conditional link from independently proved rational interval endpoints
to the unchanged original physical FF / Perron / Wilson quadrature. -/
noncomputable def p4Q2PZ37AFV_toOriginalReceiverQuadrature
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c) :
    p4Q2PZ37AFJ_originalReceiverQuadrature H e lo hi c :=
  p4Q2PZ37AFT_toOriginalReceiverQuadrature H e c hlo
    (p4Q2PZ37AFV_toOriginalVerifiedSamples H e c t)

noncomputable def p4Q2PZ37AFV_toOriginalCoefficientVariance
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (hlo : 0 ≤ lo)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c) :
    p4Q2PZ37AFI_originalCoefficientVarianceCertificate H e lo hi c :=
  p4Q2PZ37AFT_toOriginalCoefficientVarianceCertificate H e c hlo
    (p4Q2PZ37AFV_toOriginalVerifiedSamples H e c t)

/-- Positive endpoint at an actually verified original receiver interval
guarantees true positive receiver at that actual SU(2) grid center. -/
theorem p4Q2PZ37AFV_originalReceiver_center_positive
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (i : Fin (Fintype.card Grid))
    (h : 0 < (t.receiver a ha i).lower) :
    0 < F e a (gridCenter i) :=
  p4Q2PZ37AFV_interval_positive (t.receiver a ha i) h

theorem p4Q2PZ37AFV_originalReceiver_center_negative
    (e : Link) {lo hi : ℝ}
    (c : p4Q2PZ37AFG_originalShellSampleTable H e lo hi)
    (t : p4Q2PZ37AFV_originalFiniteIntervalInput H e lo hi c)
    (a : Pair) (ha : a ∈ c.s) (i : Fin (Fintype.card Grid))
    (h : (t.receiver a ha i).upper < 0) :
    F e a (gridCenter i) < 0 :=
  p4Q2PZ37AFV_interval_negative (t.receiver a ha i) h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFV_interval_ordered
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFV_intervalToBall
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFV_interval_positive
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFV_interval_negative
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFV_ballSquare
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AFV_ballMul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFV_toOriginalVerifiedSamples
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFV_toOriginalReceiverQuadrature
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFV_toOriginalCoefficientVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFV_originalReceiver_center_positive
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AFV_originalReceiver_center_negative
