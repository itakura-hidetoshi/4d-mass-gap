import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSTimeAverage
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.NNReal.Lemmas
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

/-- The Bochner primitive of a completed physical semigroup orbit. -/
def timePrimitive
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (r : ℝ) : P.PhysicalHilbert :=
  ∫ s in (0 : ℝ)..r, T.realPhysicalOrbit psi s

@[simp] theorem timePrimitive_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.timePrimitive psi 0 = 0 := by
  simp [timePrimitive]

/-- The physical orbit is the derivative of its Bochner primitive. -/
theorem timePrimitive_hasDerivAt
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (r : ℝ) :
    HasDerivAt (T.timePrimitive psi)
      (T.realPhysicalOrbit psi r) r := by
  simpa only [timePrimitive] using
    ((T.realPhysicalOrbit_continuous psi).integral_hasStrictDerivAt 0 r).hasDerivAt

/-- Coercion from nonnegative reals to reals preserves the right-neighborhood
filter at zero. -/
theorem nnreal_coe_tendsto_zero_right :
    Tendsto (fun h : NNReal => (h : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 (Ioi 0)) := by
  change Filter.map NNReal.toReal (𝓝[>] (0 : NNReal)) ≤ 𝓝[>] (0 : ℝ)
  rw [NNReal.map_coe_nhdsGT]

/-- The normalized positive-time averages converge strongly to the original
physical vector as the averaging width tends to zero from the right. -/
theorem timeAverage_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Tendsto (fun h : NNReal => T.timeAverage h psi)
      (nhdsWithin 0 (Ioi 0)) (nhds psi) := by
  have hreal :=
    (T.timePrimitive_hasDerivAt psi 0).tendsto_slope_zero_right
  have hcomp := hreal.comp nnreal_coe_tendsto_zero_right
  simpa [timeAverage, timeIntegral, timePrimitive] using hcomp

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
