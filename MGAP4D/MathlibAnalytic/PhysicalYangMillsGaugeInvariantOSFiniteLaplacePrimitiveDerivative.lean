import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteLaplaceIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The exponentially renormalized moving-interval primitive associated with a
finite Laplace integral.  It is the real-time expression naturally obtained
by applying the semigroup to the finite Laplace integral. -/
def shiftedExponentialTimePrimitive
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert)
    (r : ℝ) : P.PhysicalHilbert :=
  Real.exp (lambda * r) •
    (T.exponentialTimePrimitive lambda psi ((h : ℝ) + r) -
      T.exponentialTimePrimitive lambda psi r)

@[simp] theorem shiftedExponentialTimePrimitive_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.shiftedExponentialTimePrimitive lambda h psi 0 =
      T.finiteLaplaceIntegral lambda h psi := by
  simp [shiftedExponentialTimePrimitive, finiteLaplaceIntegral]

/-- The scalar exponential prefactor has derivative `lambda` at zero. -/
theorem exponentialPrefactor_hasDerivAt_zero
    (lambda : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (lambda * r)) lambda 0 := by
  have hlinear : HasDerivAt (fun r : ℝ => lambda * r) lambda 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_mul lambda
  simpa using hlinear.exp

/-- The moving interval in the weighted primitive has derivative equal to the
weighted endpoint difference. -/
theorem exponentialMovingInterval_hasDerivAt_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    HasDerivAt
      (fun r : ℝ =>
        T.exponentialTimePrimitive lambda psi ((h : ℝ) + r) -
          T.exponentialTimePrimitive lambda psi r)
      (T.exponentiallyWeightedPhysicalOrbit lambda psi (h : ℝ) - psi)
      0 := by
  have harg : HasDerivAt (fun r : ℝ => (h : ℝ) + r) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (h : ℝ)
  have hshift :
      HasDerivAt
        (fun r : ℝ =>
          T.exponentialTimePrimitive lambda psi ((h : ℝ) + r))
        (T.exponentiallyWeightedPhysicalOrbit lambda psi (h : ℝ)) 0 := by
    have hout :=
      T.exponentialTimePrimitive_hasDerivAt lambda psi ((h : ℝ) + 0)
    have hcomp := hout.scomp 0 harg
    simpa using hcomp
  have hzero :
      HasDerivAt (T.exponentialTimePrimitive lambda psi) psi 0 := by
    simpa using T.exponentialTimePrimitive_hasDerivAt lambda psi 0
  exact hshift.sub hzero

/-- The derivative at zero of the shifted exponential primitive is the finite
Laplace resolvent expression
`lambda R_{lambda,h} psi + exp(-lambda h) T_h psi - psi`. -/
theorem shiftedExponentialTimePrimitive_hasDerivAt_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    HasDerivAt (T.shiftedExponentialTimePrimitive lambda h psi)
      (lambda • T.finiteLaplaceIntegral lambda h psi +
        T.exponentiallyWeightedPhysicalOrbit lambda psi (h : ℝ) - psi)
      0 := by
  have hscalar := exponentialPrefactor_hasDerivAt_zero lambda
  have hinterval :=
    T.exponentialMovingInterval_hasDerivAt_zero lambda h psi
  have hproduct := hscalar.smul hinterval
  have hfun :
      T.shiftedExponentialTimePrimitive lambda h psi =
        (fun r : ℝ =>
          Real.exp (lambda * r) •
            (T.exponentialTimePrimitive lambda psi (r + (h : ℝ)) -
              T.exponentialTimePrimitive lambda psi r)) := by
    funext r
    simp [shiftedExponentialTimePrimitive, add_comm]
  rw [hfun]
  convert hproduct using 1
  · simp only [finiteLaplaceIntegral, mul_zero, Real.exp_zero,
      one_smul, add_zero, T.exponentialTimePrimitive_zero, sub_zero] <;>
      module

/-- The derivative formula with the terminal term written directly in completed
semigroup notation. -/
theorem shiftedExponentialTimePrimitive_hasDerivAt_zero_explicit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    HasDerivAt (T.shiftedExponentialTimePrimitive lambda h psi)
      (lambda • T.finiteLaplaceIntegral lambda h psi +
        Real.exp ((-lambda) * (h : ℝ)) •
          T.toPhysicalSemigroup.operator h psi - psi)
      0 := by
  simpa [exponentiallyWeightedPhysicalOrbit, realPhysicalOrbit] using
    T.shiftedExponentialTimePrimitive_hasDerivAt_zero lambda h psi

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
