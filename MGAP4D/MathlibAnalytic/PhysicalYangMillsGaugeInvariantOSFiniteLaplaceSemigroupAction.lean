import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFiniteLaplacePrimitiveDerivative
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

/-- Completed Euclidean-time evolution shifts a weighted orbit and produces
its compensating exponential factor. -/
theorem physicalOperator_exponentiallyWeightedPhysicalOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (t : NNReal) (psi : P.PhysicalHilbert)
    (s : ℝ) (hs : 0 ≤ s) :
    T.toPhysicalSemigroup.operator t
        (T.exponentiallyWeightedPhysicalOrbit lambda psi s) =
      Real.exp (lambda * (t : ℝ)) •
        T.exponentiallyWeightedPhysicalOrbit lambda psi
          (s + (t : ℝ)) := by
  calc
    T.toPhysicalSemigroup.operator t
        (T.exponentiallyWeightedPhysicalOrbit lambda psi s) =
      Real.exp ((-lambda) * s) •
        T.toPhysicalSemigroup.operator t (T.realPhysicalOrbit psi s) := by
          simp [exponentiallyWeightedPhysicalOrbit, map_smul]
    _ = Real.exp ((-lambda) * s) •
        T.realPhysicalOrbit
          (T.toPhysicalSemigroup.operator t psi) s := by
          rw [T.physicalOperator_realPhysicalOrbit]
    _ = Real.exp ((-lambda) * s) •
        T.realPhysicalOrbit psi (s + (t : ℝ)) := by
          rw [T.realPhysicalOrbit_operator_eq_add_of_nonneg t psi s hs]
    _ = Real.exp (lambda * (t : ℝ)) •
        T.exponentiallyWeightedPhysicalOrbit lambda psi
          (s + (t : ℝ)) := by
          rw [exponentiallyWeightedPhysicalOrbit, smul_smul]
          congr 1
          rw [← Real.exp_add]
          congr 1
          ring

/-- Applying the semigroup to a finite Laplace integral gives the shifted
exponential primitive. -/
theorem physicalOperator_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (t h : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator t
        (T.finiteLaplaceIntegral lambda h psi) =
      T.shiftedExponentialTimePrimitive lambda h psi (t : ℝ) := by
  unfold finiteLaplaceIntegral exponentialTimePrimitive
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (T.toPhysicalSemigroup.operator t)
    (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
      lambda psi 0 (h : ℝ))]
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
        T.toPhysicalSemigroup.operator t
          (T.exponentiallyWeightedPhysicalOrbit lambda psi s)) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        Real.exp (lambda * (t : ℝ)) •
          T.exponentiallyWeightedPhysicalOrbit lambda psi
            (s + (t : ℝ)) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hh : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
          rw [uIcc_of_le hh] at hs
          exact T.physicalOperator_exponentiallyWeightedPhysicalOrbit
            lambda t psi s hs.1
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (0 : ℝ)..(h : ℝ),
          T.exponentiallyWeightedPhysicalOrbit lambda psi
            (s + (t : ℝ))) := by
          rw [intervalIntegral.integral_smul]
    _ = Real.exp (lambda * (t : ℝ)) •
        (∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
          T.exponentiallyWeightedPhysicalOrbit lambda psi s) := by
          rw [intervalIntegral.integral_comp_add_right]
          simp
    _ = T.shiftedExponentialTimePrimitive lambda h psi (t : ℝ) := by
          unfold shiftedExponentialTimePrimitive exponentialTimePrimitive
          congr 1
          symm
          simpa [add_comm] using
            intervalIntegral.integral_interval_sub_left
              (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
                lambda psi 0 ((t : ℝ) + (h : ℝ)))
              (T.exponentiallyWeightedPhysicalOrbit_intervalIntegrable
                lambda psi 0 (t : ℝ))

/-- The right difference quotient of a finite Laplace integral is the slope of
its shifted exponential primitive. -/
theorem rightDifferenceQuotient_finiteLaplaceIntegral
    (T : P.StronglyContinuousPhysicalSemigroup)
    (lambda : ℝ) (h t : NNReal) (psi : P.PhysicalHilbert) :
    T.rightDifferenceQuotient
        (T.finiteLaplaceIntegral lambda h psi) t =
      (t : ℝ)⁻¹ •
        (T.shiftedExponentialTimePrimitive lambda h psi (t : ℝ) -
          T.shiftedExponentialTimePrimitive lambda h psi 0) := by
  unfold rightDifferenceQuotient
  rw [T.physicalOperator_finiteLaplaceIntegral]
  rw [T.shiftedExponentialTimePrimitive_zero]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
