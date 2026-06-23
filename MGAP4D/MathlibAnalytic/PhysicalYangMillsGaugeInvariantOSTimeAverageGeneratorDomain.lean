import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverageConvergence
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

@[simp] theorem timeIntegral_eq_timePrimitive
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.timeIntegral h psi = T.timePrimitive psi (h : ℝ) :=
  rfl

/-- On a nonnegative real time, evolving an already evolved vector adds the two
nonnegative times inside the real orbit. -/
theorem realPhysicalOrbit_operator_eq_add_of_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t : NNReal) (psi : P.PhysicalHilbert)
    (s : ℝ) (hs : 0 ≤ s) :
    T.realPhysicalOrbit (T.toPhysicalSemigroup.operator t psi) s =
      T.realPhysicalOrbit psi (s + (t : ℝ)) := by
  unfold realPhysicalOrbit
  have hs_to : s.toNNReal = ⟨s, hs⟩ := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg hs]
  have hsum :
      (s + (t : ℝ)).toNNReal = (⟨s, hs⟩ : NNReal) + t := by
    apply NNReal.eq
    simp [Real.toNNReal_of_nonneg (add_nonneg hs t.coe_nonneg)]
  rw [hs_to, hsum, T.toPhysicalSemigroup.operator_add]
  rfl

/-- Integrating an evolved vector over `[0,h]` is the same as integrating the
original orbit over the translated interval `[t,t+h]`. -/
theorem timeIntegral_operator_eq_shifted
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t h : NNReal) (psi : P.PhysicalHilbert) :
    T.timeIntegral h (T.toPhysicalSemigroup.operator t psi) =
      ∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ), T.realPhysicalOrbit psi s := by
  unfold timeIntegral
  calc
    (∫ s in (0 : ℝ)..(h : ℝ),
        T.realPhysicalOrbit (T.toPhysicalSemigroup.operator t psi) s) =
      ∫ s in (0 : ℝ)..(h : ℝ),
        T.realPhysicalOrbit psi (s + (t : ℝ)) := by
          apply intervalIntegral.integral_congr
          intro s hs
          have hh : (0 : ℝ) ≤ (h : ℝ) := h.coe_nonneg
          rw [uIcc_of_le hh] at hs
          exact T.realPhysicalOrbit_operator_eq_add_of_nonneg t psi s hs.1
    _ = ∫ s in (0 : ℝ) + (t : ℝ)..(h : ℝ) + (t : ℝ),
        T.realPhysicalOrbit psi s := by
          rw [intervalIntegral.integral_comp_add_right]
    _ = ∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
        T.realPhysicalOrbit psi s := by simp

/-- Evolution of the unnormalized average is a difference of two primitive
values. -/
theorem physicalOperator_timeIntegral_eq_timePrimitive_sub
    (T : P.StronglyContinuousPhysicalSemigroup)
    (t h : NNReal) (psi : P.PhysicalHilbert) :
    T.toPhysicalSemigroup.operator t (T.timeIntegral h psi) =
      T.timePrimitive psi ((h : ℝ) + (t : ℝ)) -
        T.timePrimitive psi (t : ℝ) := by
  calc
    T.toPhysicalSemigroup.operator t (T.timeIntegral h psi) =
        T.timeIntegral h (T.toPhysicalSemigroup.operator t psi) :=
      T.physicalOperator_timeIntegral t h psi
    _ = ∫ s in (t : ℝ)..(h : ℝ) + (t : ℝ),
        T.realPhysicalOrbit psi s :=
      T.timeIntegral_operator_eq_shifted t h psi
    _ = T.timePrimitive psi ((h : ℝ) + (t : ℝ)) -
        T.timePrimitive psi (t : ℝ) := by
      unfold timePrimitive
      symm
      simpa [add_comm] using
        intervalIntegral.integral_interval_sub_left
          (T.realPhysicalOrbit_intervalIntegrable psi 0
            ((t : ℝ) + (h : ℝ)))
          (T.realPhysicalOrbit_intervalIntegrable psi 0 (t : ℝ))

/-- The moving interval integral whose derivative controls the generator value
of a fixed-width time average. -/
def shiftedTimeIntegralPrimitive
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) (r : ℝ) : P.PhysicalHilbert :=
  T.timePrimitive psi ((h : ℝ) + r) - T.timePrimitive psi r

/-- The derivative of the moving interval integral at zero is the endpoint
difference `T_h psi - psi`. -/
theorem shiftedTimeIntegralPrimitive_hasDerivAt_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    HasDerivAt (T.shiftedTimeIntegralPrimitive h psi)
      (T.toPhysicalSemigroup.operator h psi - psi) 0 := by
  have harg : HasDerivAt (fun r : ℝ => (h : ℝ) + r) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (h : ℝ)
  have hshift :
      HasDerivAt (fun r : ℝ => T.timePrimitive psi ((h : ℝ) + r))
        (T.realPhysicalOrbit psi (h : ℝ)) 0 := by
    simpa using (T.timePrimitive_hasDerivAt psi (h : ℝ)).comp 0 harg
  have hzero := T.timePrimitive_hasDerivAt psi 0
  simpa [shiftedTimeIntegralPrimitive, realPhysicalOrbit] using
    hshift.sub hzero

/-- The right difference quotient of a time average is the normalized slope of
the moving interval primitive. -/
theorem rightDifferenceQuotient_timeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h t : NNReal) (psi : P.PhysicalHilbert) :
    T.rightDifferenceQuotient (T.timeAverage h psi) t =
      (h : ℝ)⁻¹ •
        ((t : ℝ)⁻¹ •
          (T.shiftedTimeIntegralPrimitive h psi (t : ℝ) -
            T.shiftedTimeIntegralPrimitive h psi 0)) := by
  simp only [rightDifferenceQuotient, timeAverage, map_smul,
    T.physicalOperator_timeIntegral_eq_timePrimitive_sub,
    T.timeIntegral_eq_timePrimitive]
  rw [T.timePrimitive_zero]
  unfold shiftedTimeIntegralPrimitive
  module

/-- Every fixed-width time average admits the expected right generator value. -/
theorem hasRightGeneratorValue_timeAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.HasRightGeneratorValue (T.timeAverage h psi)
      ((h : ℝ)⁻¹ •
        (T.toPhysicalSemigroup.operator h psi - psi)) := by
  unfold HasRightGeneratorValue
  have hreal :=
    (T.shiftedTimeIntegralPrimitive_hasDerivAt_zero h psi).tendsto_slope_zero_right
  have hscaled := (tendsto_const_nhds.smul hreal :
    Tendsto
      (fun r : ℝ => (h : ℝ)⁻¹ •
        (r⁻¹ •
          (T.shiftedTimeIntegralPrimitive h psi (0 + r) -
            T.shiftedTimeIntegralPrimitive h psi 0)))
      (𝓝[>] (0 : ℝ))
      (nhds ((h : ℝ)⁻¹ •
        (T.toPhysicalSemigroup.operator h psi - psi))))
  have hcomp := hscaled.comp nnreal_coe_tendsto_zero_right
  simpa only [T.rightDifferenceQuotient_timeAverage, zero_add] using hcomp

/-- Every time average belongs to the right generator domain. -/
theorem timeAverage_mem_rightGeneratorDomain
    (T : P.StronglyContinuousPhysicalSemigroup)
    (h : NNReal) (psi : P.PhysicalHilbert) :
    T.timeAverage h psi ∈ T.rightGeneratorDomain :=
  ⟨(h : ℝ)⁻¹ • (T.toPhysicalSemigroup.operator h psi - psi),
    T.hasRightGeneratorValue_timeAverage h psi⟩

/-- The generator domain is dense in the completed physical Hilbert space. -/
theorem rightGeneratorDomain_dense
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Dense (T.rightGeneratorDomain : Set P.PhysicalHilbert) := by
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_forall
  intro psi
  apply mem_closure_of_tendsto (T.timeAverage_tendsto_zero psi)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact T.timeAverage_mem_rightGeneratorDomain h psi

/-- The right Hamiltonian is therefore densely defined, since it uses the same
domain as the right generator. -/
theorem rightHamiltonianDomain_dense
    (T : P.StronglyContinuousPhysicalSemigroup) :
    Dense (T.rightGeneratorDomain : Set P.PhysicalHilbert) :=
  T.rightGeneratorDomain_dense

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
