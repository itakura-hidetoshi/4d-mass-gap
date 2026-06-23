import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSClosedRightHamiltonianRange
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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

/-- The exponentially weighted completed physical semigroup orbit used in the
finite-time Laplace resolvent construction. -/
def exponentiallyWeightedPhysicalOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) (s : ℝ) : P.PhysicalHilbert :=
  Real.exp ((-lambda) * s) • T.realPhysicalOrbit psi s

/-- Exponentially weighted physical orbits are continuous on real time. -/
theorem exponentiallyWeightedPhysicalOrbit_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) :
    Continuous (T.exponentiallyWeightedPhysicalOrbit lambda psi) := by
  have hscalar : Continuous (fun s : ℝ => Real.exp ((-lambda) * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hscalar.smul (T.realPhysicalOrbit_continuous psi)

/-- Exponentially weighted physical orbits are Bochner integrable on every
compact interval. -/
theorem exponentiallyWeightedPhysicalOrbit_intervalIntegrable
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) (a b : ℝ) :
    IntervalIntegrable (T.exponentiallyWeightedPhysicalOrbit lambda psi)
      MeasureTheory.volume a b :=
  (T.exponentiallyWeightedPhysicalOrbit_continuous lambda psi).intervalIntegrable a b

@[simp] theorem exponentiallyWeightedPhysicalOrbit_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) :
    T.exponentiallyWeightedPhysicalOrbit lambda psi 0 = psi := by
  simp [exponentiallyWeightedPhysicalOrbit]

@[simp] theorem exponentiallyWeightedPhysicalOrbit_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi phi : P.PhysicalHilbert) (s : ℝ) :
    T.exponentiallyWeightedPhysicalOrbit lambda (psi + phi) s =
      T.exponentiallyWeightedPhysicalOrbit lambda psi s +
        T.exponentiallyWeightedPhysicalOrbit lambda phi s := by
  simp [exponentiallyWeightedPhysicalOrbit, smul_add]

@[simp] theorem exponentiallyWeightedPhysicalOrbit_smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda r : ℝ) (psi : P.PhysicalHilbert) (s : ℝ) :
    T.exponentiallyWeightedPhysicalOrbit lambda (r • psi) s =
      r • T.exponentiallyWeightedPhysicalOrbit lambda psi s := by
  simp [exponentiallyWeightedPhysicalOrbit, smul_smul, mul_comm]

/-- The Bochner primitive of an exponentially weighted physical orbit. -/
def exponentialTimePrimitive
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) (r : ℝ) : P.PhysicalHilbert :=
  ∫ s in (0 : ℝ)..r, T.exponentiallyWeightedPhysicalOrbit lambda psi s

@[simp] theorem exponentialTimePrimitive_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) :
    T.exponentialTimePrimitive lambda psi 0 = 0 := by
  simp [exponentialTimePrimitive]

/-- The weighted physical orbit is the derivative of its Bochner primitive. -/
theorem exponentialTimePrimitive_hasDerivAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) (r : ℝ) :
    HasDerivAt (T.exponentialTimePrimitive lambda psi)
      (T.exponentiallyWeightedPhysicalOrbit lambda psi r) r := by
  simpa only [exponentialTimePrimitive] using
    ((T.exponentiallyWeightedPhysicalOrbit_continuous lambda psi).integral_hasStrictDerivAt
      0 r).hasDerivAt

/-- The finite-time Laplace integral of a completed physical orbit. -/
def finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) : P.PhysicalHilbert :=
  T.exponentialTimePrimitive lambda psi (h : ℝ)

@[simp] theorem finiteLaplaceIntegral_zero_width
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (psi : P.PhysicalHilbert) :
    T.finiteLaplaceIntegral lambda 0 psi = 0 := by
  simp [finiteLaplaceIntegral]

@[simp] theorem finiteLaplaceIntegral_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) :
    T.finiteLaplaceIntegral lambda h 0 = 0 := by
  simp [finiteLaplaceIntegral, exponentialTimePrimitive,
    exponentiallyWeightedPhysicalOrbit, realPhysicalOrbit]

@[simp] theorem finiteLaplaceIntegral_add
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi phi : P.PhysicalHilbert) :
    T.finiteLaplaceIntegral lambda h (psi + phi) =
      T.finiteLaplaceIntegral lambda h psi +
        T.finiteLaplaceIntegral lambda h phi := by
  unfold finiteLaplaceIntegral exponentialTimePrimitive
  simpa only [exponentiallyWeightedPhysicalOrbit_add] using
    intervalIntegral.integral_add
      (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
        lambda psi 0 (h : ℝ))
      (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
        lambda phi 0 (h : ℝ))

@[simp] theorem finiteLaplaceIntegral_smul
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (r : ℝ) (psi : P.PhysicalHilbert) :
    T.finiteLaplaceIntegral lambda h (r • psi) =
      r • T.finiteLaplaceIntegral lambda h psi := by
  simp [finiteLaplaceIntegral, exponentialTimePrimitive,
    exponentiallyWeightedPhysicalOrbit, realPhysicalOrbit,
    smul_smul, mul_comm]

/-- The finite-time Laplace integral is a real-linear map on the completed
physical Hilbert space. -/
noncomputable def finiteLaplaceIntegralLinearMap
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) :
    P.PhysicalHilbert →ₗ[ℝ] P.PhysicalHilbert where
  toFun := T.finiteLaplaceIntegral lambda h
  map_add' := T.finiteLaplaceIntegral_add lambda h
  map_smul' := T.finiteLaplaceIntegral_smul lambda h

@[simp] theorem finiteLaplaceIntegralLinearMap_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    T.finiteLaplaceIntegralLinearMap lambda h psi =
      T.finiteLaplaceIntegral lambda h psi :=
  rfl

/-- The exponentially decaying terminal semigroup term is bounded by the
scalar exponential weight times the original norm. -/
theorem norm_exponential_terminal_le
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h : NNReal) (psi : P.PhysicalHilbert) :
    ‖Real.exp ((-lambda) * (h : ℝ)) •
        T.toPhysicalSemigroup.operator h psi‖ ≤
      Real.exp ((-lambda) * (h : ℝ)) * ‖psi‖ := by
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos ((-lambda) * (h : ℝ)))]
  exact mul_le_mul_of_nonneg_left
    (T.physicalOperator_norm_le h psi)
    (Real.exp_pos ((-lambda) * (h : ℝ))).le

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
