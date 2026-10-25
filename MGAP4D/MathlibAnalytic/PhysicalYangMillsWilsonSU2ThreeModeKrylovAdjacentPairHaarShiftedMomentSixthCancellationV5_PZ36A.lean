import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalScaledStrippedFifthAffineV5_PZ36
import Mathlib.Tactic

/-!
# P4-Q2-PZ36A — structural sixth-order cancellation for common-shift moments

A purely algebraic theorem needed BEFORE attempting to find a nonzero
original sixth Ward coefficient. Two binomial moment families sharing
the boundary shift x have an identically zero sixth minor coefficient,
even when their fifth moment gap contains an arbitrary extra LINEAR
boundary term. The parameters below are universally quantified scalars;
they are not a replacement spectrum, measure, posterior or Wilson model.

The exact 20,15,6 factors are the 720-scaled cubic/cubic,
quadratic/quartic and linear/fifth Taylor cross terms, respectively.
This proves an algebraic cancellation mechanism. Transporting the
actual two-slab Haar moments into the SAME shared coefficients remains
a separate required theorem. NO physical W6=0 theorem is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic
namespace GroundStatePosteriorJoint

noncomputable section
set_option maxHeartbeats 3900000

/-- Three-boundary determinant of two real response functions. -/
def p4Q2PZ36A_boundaryDet (f g : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (f y-f x)*(g z-g x)-(f z-f x)*(g y-g x)

/-- Binomial second moment with a common scalar boundary shift. -/
def p4Q2PZ36A_shiftedSecond (m1 m2 x : ℝ) : ℝ :=
  x^2+2*m1*x+m2

/-- Signed third Taylor moment; its minus sign is essential. -/
def p4Q2PZ36A_shiftedSignedThird (m1 m2 m3 x : ℝ) : ℝ :=
  -(x^3+3*m1*x^2+3*m2*x+m3)

/-- Binomial fourth moment of the same shifted family. -/
def p4Q2PZ36A_shiftedFourth (m1 m2 m3 m4 x : ℝ) : ℝ :=
  x^4+4*m1*x^3+6*m2*x^2+4*m3*x+m4

/-- Positive fifth-moment difference after cancellation of the shared
monic fifth power and an irrelevant boundary constant. The extra slope
k can include the genuine PZ36 affine stripped-Haar contribution. -/
def p4Q2PZ36A_mixedFifthGap
    (m1 m2 m3 m4 n1 n2 n3 n4 k x : ℝ) : ℝ :=
  5*(n1-m1)*x^4+10*(n2-m2)*x^3+10*(n3-m3)*x^2+
    (5*(n4-m4)+k)*x

/-- Universal exact cancellation of the full SIXTH Taylor minor
coefficient, not just one selected term. A later physical application
MUST establish the binomial moment representations with the SAME n's.
No nonzero/zero physical Ward or mass-gap conclusion follows by itself. -/
theorem p4Q2PZ36A_commonShift_sixthCoefficient_zero
    (m1 m2 m3 m4 n1 n2 n3 n4 k x y z : ℝ) :
    20*p4Q2PZ36A_boundaryDet
        (p4Q2PZ36A_shiftedSignedThird m1 m2 m3)
        (p4Q2PZ36A_shiftedSignedThird n1 n2 n3) x y z +
    15*(p4Q2PZ36A_boundaryDet
        (p4Q2PZ36A_shiftedSecond m1 m2)
        (p4Q2PZ36A_shiftedFourth n1 n2 n3 n4) x y z +
      p4Q2PZ36A_boundaryDet
        (p4Q2PZ36A_shiftedFourth m1 m2 m3 m4)
        (p4Q2PZ36A_shiftedSecond n1 n2) x y z) -
    6*p4Q2PZ36A_boundaryDet (fun t : ℝ => -t-m1)
        (p4Q2PZ36A_mixedFifthGap m1 m2 m3 m4 n1 n2 n3 n4 k) x y z = 0 := by
  unfold p4Q2PZ36A_boundaryDet p4Q2PZ36A_shiftedSecond
    p4Q2PZ36A_shiftedSignedThird p4Q2PZ36A_shiftedFourth
    p4Q2PZ36A_mixedFifthGap
  ring

end
end GroundStatePosteriorJoint
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ36A_commonShift_sixthCoefficient_zero
