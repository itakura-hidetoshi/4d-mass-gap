import Mathlib.Tactic

/-!
# PZ36B — common-endpoint sixth-order cancellation algebra

Both odd Taylor moments carry a minus sign. These are universal real
polynomial identities only; no original Haar transport is assumed or
asserted in this module. No new axioms or computational proof substitutes.
-/

namespace MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ36EndpointAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000

/-- Second raw moment with a common endpoint exponential. -/
def second (a b x : ℝ) : ℝ := x^2 + 2*a*x + b

/-- SIGNED third Taylor moment, not the positive raw third moment. -/
def third (a b c x : ℝ) : ℝ :=
  -(x^3 + 3*a*x^2 + 3*b*x + c)

/-- Fourth raw moment. -/
def fourth (a b c d x : ℝ) : ℝ :=
  x^4 + 4*a*x^3 + 6*b*x^2 + 4*c*x + d

/-- Oriented determinant of three-boundary differences. -/
def wedge (f g : ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (f y-f x)*(g z-g x) - (f z-f x)*(g y-g x)

def vandermonde (x y z : ℝ) : ℝ := (y-x)*(z-x)*(z-y)
def sumOne (x y z : ℝ) : ℝ := x+y+z
def sumTwo (x y z : ℝ) : ℝ :=
  x^2+y^2+z^2+x*y+x*z+y*z

/-- PX sixth coefficient of two degree-four moment jets. A boundary
constant in the second moment drops out of the difference determinant. -/
def sixthCoefficient
    (a b c d A B C D x y z : ℝ) : ℝ :=
  wedge (third a b c) (third A B C) x y z / 36 +
    (wedge (second a b) (fourth A B C D) x y z +
      wedge (fourth a b c d) (second A B) x y z) / 48

/-- The fourth-jet sixth coefficient is generally NOT zero. -/
theorem sixthCoefficient_factor
    (a b c d A B C D x y z : ℝ) :
    sixthCoefficient a b c d A B C D x y z =
      vandermonde x y z / 24 *
        ((a-A)*sumTwo x y z +
          2*(b-B)*sumOne x y z + 2*(c-C)) := by
  unfold sixthCoefficient wedge third second fourth
    vandermonde sumTwo sumOne
  ring

/-- Quartic profile difference has the same oriented Vandermonde shape. -/
theorem quarticProfile_wedge
    (b0 b1 b2 b3 b4 x y z : ℝ) :
    (y-x)*
        ((b0+b1*z+b2*z^2+b3*z^3+b4*z^4) -
          (b0+b1*x+b2*x^2+b3*x^3+b4*x^4)) -
      (z-x)*
        ((b0+b1*y+b2*y^2+b3*y^3+b4*y^4) -
          (b0+b1*x+b2*x^2+b3*x^3+b4*x^4)) =
      vandermonde x y z *
        (b2+b3*sumOne x y z+b4*sumTwo x y z) := by
  unfold vandermonde sumOne sumTwo
  ring

/-- Exact cancellation only after matching the authentic moment coefficients. -/
theorem lowSector_cancel
    (a b c d A B C D x y z : ℝ) :
    720 * sixthCoefficient a b c d A B C D x y z +
      6*(y-x)*(z-x)*(z-y)*
        (10*(C-c) + 10*(B-b)*(x+y+z) +
          5*(A-a)*(x^2+y^2+z^2+x*y+x*z+y*z)) = 0 := by
  rw [sixthCoefficient_factor]
  unfold vandermonde sumOne sumTwo
  ring

/-- Transparent coefficient transport; no integral identity is postulated. -/
theorem lowSector_cancel_of_coefficient_transport
    (a b c d A B C D x y z beta2 beta3 beta4 : ℝ)
    (h2 : beta2 = 10*(C-c))
    (h3 : beta3 = 10*(B-b))
    (h4 : beta4 = 5*(A-a)) :
    720 * sixthCoefficient a b c d A B C D x y z +
      6*(y-x)*(z-x)*(z-y)*
        (beta2 + beta3*(x+y+z) +
          beta4*(x^2+y^2+z^2+x*y+x*z+y*z)) = 0 := by
  rw [h2,h3,h4]
  exact lowSector_cancel a b c d A B C D x y z

end
end MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ36EndpointAlgebra

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ36EndpointAlgebra.sixthCoefficient_factor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ36EndpointAlgebra.quarticProfile_wedge
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ36EndpointAlgebra.lowSector_cancel
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.PZ36EndpointAlgebra.lowSector_cancel_of_coefficient_transport
