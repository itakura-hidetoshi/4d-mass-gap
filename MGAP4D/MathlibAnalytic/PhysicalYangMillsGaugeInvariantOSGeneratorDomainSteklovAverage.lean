import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalOrbitContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set MeasureTheory

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The physical Euclidean-time orbit, extended from nonnegative time to the
real line by clamping negative times to zero.  This auxiliary real-time orbit
lets us use mathlib's Bochner interval-integral API without changing the
physical semigroup parameter space. -/
def realPhysicalOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s : ℝ) : P.PhysicalHilbert :=
  T.toPhysicalSemigroup.operator (Real.toNNReal s) psi

/-- The clamped real-time physical orbit is continuous. -/
theorem realPhysicalOrbit_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous (T.realPhysicalOrbit psi) := by
  exact (T.physicalOrbit_continuous psi).comp continuous_real_toNNReal

/-- Hence every finite interval of the clamped physical orbit is Bochner
integrable. -/
theorem realPhysicalOrbit_intervalIntegrable
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (a b : ℝ) :
    IntervalIntegrable (T.realPhysicalOrbit psi) volume a b :=
  (T.realPhysicalOrbit_continuous psi).intervalIntegrable a b

/-- Steklov averaging of a physical vector over the initial Euclidean-time
interval `[0,h]`.  Positive `h` will be used to produce vectors in the right
infinitesimal-generator domain. -/
noncomputable def steklovAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (h : NNReal) : P.PhysicalHilbert :=
  (h : ℝ)⁻¹ •
    ∫ s in (0 : ℝ)..(h : ℝ), T.realPhysicalOrbit psi s

@[simp] theorem steklovAverage_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.steklovAverage psi 0 = 0 := by
  simp [steklovAverage]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
