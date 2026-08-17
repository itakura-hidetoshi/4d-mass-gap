import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPhysicalOrbitContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The physical Euclidean-time orbit, extended from nonnegative time to the
real line by clamping negative times to zero.  This auxiliary real-time orbit
lets the generator-density route use mathlib's Bochner interval integrals
without changing the physical semigroup parameter space. -/
def generatorDensityRealOrbit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (s : ℝ) : P.PhysicalHilbert :=
  T.toPhysicalSemigroup.operator (Real.toNNReal s) psi

/-- The clamped real-time orbit used in the generator-density route is
continuous. -/
theorem generatorDensityRealOrbit_continuous
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    Continuous (T.generatorDensityRealOrbit psi) := by
  exact (T.physicalOrbit_continuous psi).comp continuous_real_toNNReal

/-- Every finite interval of the clamped orbit is Bochner integrable. -/
theorem generatorDensityRealOrbit_intervalIntegrable
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (a b : ℝ) :
    IntervalIntegrable (T.generatorDensityRealOrbit psi) volume a b :=
  (T.generatorDensityRealOrbit_continuous psi).intervalIntegrable a b

/-- Initial-interval Steklov averaging used to construct a dense family of
vectors in the right infinitesimal-generator domain. -/
noncomputable def generatorDensitySteklovAverage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) (h : NNReal) : P.PhysicalHilbert :=
  (h : ℝ)⁻¹ •
    ∫ s in (0 : ℝ)..(h : ℝ), T.generatorDensityRealOrbit psi s

@[simp] theorem generatorDensitySteklovAverage_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (psi : P.PhysicalHilbert) :
    T.generatorDensitySteklovAverage psi 0 = 0 := by
  simp [generatorDensitySteklovAverage]

end StronglyContinuousPhysicalSemigroup

end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
