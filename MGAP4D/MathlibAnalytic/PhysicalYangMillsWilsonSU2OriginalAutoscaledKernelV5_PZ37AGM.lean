import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRefinableCouplingV5_PZ37AGK
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalRationalActionV5_PZ37AGL
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGM — original kernel from exact actions with automatic rational scaling

AGL gives the exact original rational one-slab action for every actual
rational-coordinate configuration. AGK gives a refinable interval for the
same original fixed coupling. AGJ encloses the actual exponential, but its
interface asks for a positive scale and two small-endpoint proofs.

AGM supplies these obligations from the actual rational data. For any
rational exponent endpoints lo,hi, choose

  k = Nat.ceil (max |lo| |hi|) + 1.

Then k>0 and |lo/k|,|hi/k|<=1 without an external scale hypothesis.
The original action nonnegativity proves that AGL's exact singleton has
nonnegative lower endpoint. Thus the only numerical orders supplied are
coupling order m and positive Taylor order n. Clip the resulting verified
kernel interval to [0,1] using the ORIGINAL kernel positivity and upper
bound. The AFQ 24-center specialization needs neither an action-value
oracle nor manually supplied exponent-size conditions.

Plan implemented: rational scale regression; generic scale soundness;
original exact-action nonnegativity; AGK/AGL/AGJ integration; physical
[0,1] tightening; genuine 24-center interval and AGA ball.

The canonical finite-list enumeration remains noncomputable. This does
not execute a large-volume table or claim a joint error-convergence rate,
true Haar cell masses, centered-source mean, nonzero signed transfer,
two-threshold shell, volume-uniform coercivity, Hamiltonian or continuum
Yang--Mills mass gap. The original model, root and pins are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Computable positive scale from supplied rational endpoints only. -/
def p4Q2PZ37AGM_autoScale (lo hi : ℚ) : ℕ :=
  Nat.ceil (max |lo| |hi|) + 1

theorem p4Q2PZ37AGM_autoScale_pos (lo hi : ℚ) :
    0 < p4Q2PZ37AGM_autoScale lo hi := by
  unfold p4Q2PZ37AGM_autoScale
  exact Nat.zero_lt_succ _

/-- Both endpoint obligations hold for arbitrary signs and magnitudes. -/
theorem p4Q2PZ37AGM_scaledEndpoints (lo hi : ℚ) :
    |lo / (p4Q2PZ37AGM_autoScale lo hi : ℚ)| ≤ 1 ∧
      |hi / (p4Q2PZ37AGM_autoScale lo hi : ℚ)| ≤ 1 := by
  have hk : (0 : ℚ) < (p4Q2PZ37AGM_autoScale lo hi : ℚ) := by
    exact_mod_cast p4Q2PZ37AGM_autoScale_pos lo hi
  have hc : max |lo| |hi| ≤ (Nat.ceil (max |lo| |hi|) : ℚ) := Nat.le_ceil _
  have hb : max |lo| |hi| ≤ (p4Q2PZ37AGM_autoScale lo hi : ℚ) := by
    unfold p4Q2PZ37AGM_autoScale
    push_cast
    linarith only [hc]
  constructor
  · rw [abs_div, abs_of_pos hk]
    exact (div_le_one hk).mpr ((le_max_left _ _).trans hb)
  · rw [abs_div, abs_of_pos hk]
    exact (div_le_one hk).mpr ((le_max_right _ _).trans hb)

/-- Zero and nonintegral endpoints exercise the genuine rational ceiling. -/
theorem p4Q2PZ37AGM_autoScale_checked :
    p4Q2PZ37AGM_autoScale 0 0 = 1 ∧
      p4Q2PZ37AGM_autoScale (-(3 / 2)) (7 / 3) = 4 := by
  norm_num [p4Q2PZ37AGM_autoScale]

noncomputable section

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "Grid" => p4Q2PZ37AFQ_GridIndex
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0

/-- Nonnegativity belongs to the original action and transfers to its
exact rational value; it is not a new caller-supplied premise. -/
theorem p4Q2PZ37AGM_originalActionRational_nonneg
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e)) :
    0 ≤ p4Q2PZ37AGL_slabActionRational H A B a b := by
  have h := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_nonneg
    H 2 (by norm_num) A B
  rw [p4Q2PZ37AGL_originalSlabAction_exact H A B a b] at h
  exact_mod_cast h

/-- Original exact action -> original refined coupling -> genuine Taylor
kernel enclosure, with no action oracle or external scale conditions. -/
def p4Q2PZ37AGM_originalRationalKernelInterval
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (K A B) := by
  let s := p4Q2PZ37AGL_originalSlabActionSingleton H A B a b
  have hs : 0 ≤ s.lower := p4Q2PZ37AGM_originalActionRational_nonneg H A B a b
  let lo : ℚ := -(p4Q2PZ37AGK_upper m * s.upper)
  let hi : ℚ := -(p4Q2PZ37AGK_lower m * s.lower)
  exact p4Q2PZ37AGK_originalRefinedKernelInterval H A B s hs
    m (p4Q2PZ37AGM_autoScale lo hi) n
    (p4Q2PZ37AGM_autoScale_pos lo hi) hn
    (p4Q2PZ37AGM_scaledEndpoints lo hi).1
    (p4Q2PZ37AGM_scaledEndpoints lo hi).2

/-- Intersect with the actual physical [0,1] kernel range, never replace
an independently proved interval by a weaker one. -/
def p4Q2PZ37AGM_originalClippedKernelInterval
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (K A B) := by
  let c := p4Q2PZ37AGM_originalRationalKernelInterval H A B a b m n hn
  refine { lower := max 0 c.lower, upper := min 1 c.upper, hLower := ?_, hUpper := ?_ }
  · have hp : 0 ≤ K A B :=
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos H 2 b0 A B).le
    have h := max_le hp c.hLower
    simpa using h
  · have hu : K A B ≤ 1 :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_le_one
        H 2 (by norm_num) b0 p4Q2PZ37ADC_fixedCoupling_pos.le A B
    have h := le_min hu c.hUpper
    simpa using h

/-- Every actual 24-center assignment on original spatial links now
supplies the kernel interval, with only m,n and n>0 as numerical input. -/
def p4Q2PZ37AGM_original24CenterKernelInterval
    (left right : Link → Fin (Fintype.card Grid))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval
      (K (fun e => p4Q2PZ37AFQ_originalCenters (left e))
        (fun e => p4Q2PZ37AFQ_originalCenters (right e))) :=
  p4Q2PZ37AGM_originalClippedKernelInterval H _ _
    (fun e => p4Q2PZ37AGL_originalCenter_rational (left e))
    (fun e => p4Q2PZ37AGL_originalCenter_rational (right e)) m n hn

/-- The computed endpoints certify the unchanged original kernel value. -/
theorem p4Q2PZ37AGM_original24CenterKernel_contains
    (left right : Link → Fin (Fintype.card Grid))
    (m n : ℕ) (hn : 0 < n) :
    ((p4Q2PZ37AGM_original24CenterKernelInterval H left right m n hn).lower : ℝ) ≤
      K (fun e => p4Q2PZ37AFQ_originalCenters (left e))
        (fun e => p4Q2PZ37AFQ_originalCenters (right e)) ∧
    K (fun e => p4Q2PZ37AFQ_originalCenters (left e))
        (fun e => p4Q2PZ37AFQ_originalCenters (right e)) ≤
      ((p4Q2PZ37AGM_original24CenterKernelInterval H left right m n hn).upper : ℝ) :=
  ⟨(p4Q2PZ37AGM_original24CenterKernelInterval H left right m n hn).hLower,
    (p4Q2PZ37AGM_original24CenterKernelInterval H left right m n hn).hUpper⟩

/-- Retain AGA's original-value rational ball interface. -/
def p4Q2PZ37AGM_original24CenterKernelBall
    (left right : Link → Fin (Fintype.card Grid))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGA_rationalBall
      (K (fun e => p4Q2PZ37AFQ_originalCenters (left e))
        (fun e => p4Q2PZ37AFQ_originalCenters (right e))) :=
  p4Q2PZ37AGA_fromVerifiedInterval
    (p4Q2PZ37AGM_original24CenterKernelInterval H left right m n hn)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGM_autoScale_pos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGM_scaledEndpoints
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGM_autoScale_checked
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGM_originalActionRational_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGM_originalRationalKernelInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGM_originalClippedKernelInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGM_original24CenterKernelInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGM_original24CenterKernel_contains
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGM_original24CenterKernelBall
