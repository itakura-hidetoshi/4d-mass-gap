import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSeventhPhysicalCoefficientV5_PZ37B
import Mathlib.Tactic

/-!
# P4-Q2-PZ37C — exact Vandermonde and sixth stripped-Haar obstruction algebra

PZ37B gives the correct genuine sixth-action-moment Taylor jet coefficient.
This module recovers the earlier Vandermonde route as a universal identity
for two original-style common-endpoint binomial moment families.

The two fifth stripped moment slopes are p and q; the two sixth stripped
moments are arbitrary functions u and v. Keeping u and v arbitrary
isolates exactly the extra sixth-Haar obstruction, rather than assuming
the physical sixth Haar moments are affine in the endpoint Wilson action.

The conditional specialization p=15/32 and q=15/16 yields -V/512 iff
the sixth Haar wedge vanishes. These numerical slope hypotheses are NOT
presented as true source-level theorems for the original two-slab Wilson
model. Genuine SU(2) Haar transport is a separate next step.

No new axiom, sorry, admit, native_decide, surrogate posterior or
unproved rank-three/mass-gap assertion.
-/

namespace MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ37VandermondeAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

def wedge (f h : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (f y - f x) * (h z - h x) -
    (f z - f x) * (h y - h x)

def vandermonde (x y z : ℝ) : ℝ :=
  (y-x)*(z-x)*(z-y)

def first (a x : ℝ) : ℝ := x+a

def second (a b x : ℝ) : ℝ := x^2 + 2*a*x + b

def third (a b c x : ℝ) : ℝ :=
  x^3 + 3*a*x^2 + 3*b*x + c

def fourth (a b c d x : ℝ) : ℝ :=
  x^4 + 4*a*x^3 + 6*b*x^2 + 4*c*x + d

/-- Physical common-shift fifth raw moment if the genuine stripped
fifth moment differs from its identity value by slope*x. -/
def fifth (a b c d e slope x : ℝ) : ℝ :=
  x^5 + 5*a*x^4 + 10*b*x^3 + 10*c*x^2 +
    (5*d+slope)*x + e

/-- Sixth raw moment keeps its genuinely source-dependent stripped
sixth Haar moment as an ARBITRARY boundary function; no affineness. -/
def sixth (a b c d e slope : ℝ) (stripped6 : ℝ → ℝ)
    (x : ℝ) : ℝ :=
  x^6 + 6*a*x^5 + 15*b*x^4 + 20*c*x^3 +
    (15*d+6*slope)*x^2 + 6*e*x + stripped6 x

/-- The exact degree-seven signed Taylor determinant obtained from
the authentic factorials 1!6!, 2!5! and 3!4! and their reversals.
The raw moments use the original Wilson-type common scalar endpoint shift;
their physical instantiation requires independent Haar identities. -/
def seventh
    (a b c d e A B C D E p q : ℝ)
    (u v : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  -(wedge (first a) (sixth A B C D E q v) x y z)/720 -
  (wedge (second a b) (fifth A B C D E q) x y z)/240 -
  (wedge (third a b c) (fourth A B C D) x y z)/144 -
  (wedge (fourth a b c d) (third A B C) x y z)/144 -
  (wedge (fifth a b c d e p) (second A B) x y z)/240 -
  (wedge (sixth a b c d e p u) (first A) x y z)/720

/-- The PREVIOUS Vandermonde calculation becomes an exact theorem once
the previously omitted sixth stripped-Haar obstruction is retained.
There are no assumptions that u or v is affine or constant. -/
theorem seventh_vandermonde_with_sixth_obstruction
    (a b c d e A B C D E p q : ℝ)
    (u v : ℝ → ℝ) (x y z : ℝ) :
    seventh a b c d e A B C D E p q u v x y z =
      - (q-p)/240 * vandermonde x y z -
        wedge (fun t : ℝ => t) (fun t => v t-u t) x y z /720 := by
  unfold seventh wedge vandermonde first second third fourth fifth sixth
  ring

/-- For the PREVIOUS proposed fifth slopes, the -V/512 formula is
equivalent to VANISHING of the true sixth stripped-moment wedge.
The slope premises are explicitly conditional, not physical facts. -/
theorem seventh_eq_negative_vandermonde_512_iff
    (a b c d e A B C D E p q : ℝ)
    (u v : ℝ → ℝ) (x y z : ℝ)
    (hp : p = 15/32) (hq : q = 15/16) :
    seventh a b c d e A B C D E p q u v x y z =
      -(vandermonde x y z)/512 ↔
    wedge (fun t : ℝ => t) (fun t => v t-u t) x y z = 0 := by
  rw [seventh_vandermonde_with_sixth_obstruction]
  have hcoef :
      -(q-p)/240 * vandermonde x y z =
        -(vandermonde x y z)/512 := by
    rw [hp, hq]
    ring
  rw [hcoef]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

/-- Actual geometric nondegeneracy is still an independent physical
boundary-selection task. Given distinct endpoint actions and a
vanishing sixth wedge, the conditional scalar coefficient is nonzero. -/
theorem seventh_nonzero_of_distinct_actions
    (a b c d e A B C D E p q : ℝ)
    (u v : ℝ → ℝ) (x y z : ℝ)
    (hp : p = 15/32) (hq : q = 15/16)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hSixth :
      wedge (fun t : ℝ => t) (fun t => v t-u t) x y z = 0) :
    seventh a b c d e A B C D E p q u v x y z ≠ 0 := by
  have hc := (seventh_eq_negative_vandermonde_512_iff
      a b c d e A B C D E p q u v x y z hp hq).mpr hSixth
  rw [hc]
  have hv : vandermonde x y z ≠ 0 := by
    unfold vandermonde
    exact mul_ne_zero
      (mul_ne_zero (sub_ne_zero.mpr hxy.symm)
        (sub_ne_zero.mpr hxz.symm))
      (sub_ne_zero.mpr hyz.symm)
  exact div_ne_zero (neg_ne_zero.mpr hv) (by norm_num)

end
end MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ37VandermondeAlgebra

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ37VandermondeAlgebra.seventh_vandermonde_with_sixth_obstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ37VandermondeAlgebra.seventh_eq_negative_vandermonde_512_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ37VandermondeAlgebra.seventh_nonzero_of_distinct_actions
