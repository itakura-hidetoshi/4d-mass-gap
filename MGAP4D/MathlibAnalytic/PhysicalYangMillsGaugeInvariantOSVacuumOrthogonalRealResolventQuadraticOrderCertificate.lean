import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventQuadraticAbsolutelyMonotone

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff

namespace MGAP4D
namespace MathlibAnalytic

/-- A first-and-second-order certificate extracted from absolute monotonicity.
It records positivity, nonnegative slope, and nonnegative curvature on the
relevant real domain without depending on a version-specific convexity API. -/
def RealPositiveIncreasingConvexCertificate
    (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  (∀ x, x ∈ s → 0 ≤ f x) ∧
  (∀ x, x ∈ s → 0 ≤ iteratedDerivWithin 1 f s x) ∧
  (∀ x, x ∈ s → 0 ≤ iteratedDerivWithin 2 f s x)

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

set_option maxHeartbeats 1200000

/-- Absolute monotonicity canonically yields the zeroth-, first-, and
second-order order certificate. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_orderCertificate
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert) :
    RealPositiveIncreasingConvexCertificate
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) := by
  have hmono :=
    G.vacuumOrthogonalRealResolventQuadraticOn_realAbsolutelyMonotoneOn
      T hP hSelf y
  refine ⟨?_, ?_, ?_⟩
  · intro lambda hlambda
    simpa only [iteratedDerivWithin_zero] using hmono.2 0 lambda hlambda
  · intro lambda hlambda
    exact hmono.2 1 lambda hlambda
  · intro lambda hlambda
    exact hmono.2 2 lambda hlambda

/-- The scalar excitation resolvent has nonnegative first derivative throughout
the open sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_firstDerivative_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    0 ≤ iteratedDerivWithin 1
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) lambda :=
  (G.vacuumOrthogonalRealResolventQuadraticOn_orderCertificate
    T hP hSelf y).2.1 lambda hlambda

/-- The scalar excitation resolvent has nonnegative second derivative throughout
the open sub-mass interval. -/
theorem FiniteVolumeVacuumGapTransfer.vacuumOrthogonalRealResolventQuadraticOn_secondDerivative_nonneg
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.FiniteVolumeVacuumGapTransfer)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (y : P.VacuumOrthogonalHilbert)
    {lambda : ℝ} (hlambda : lambda < G.mass) :
    0 ≤ iteratedDerivWithin 2
      (G.vacuumOrthogonalRealResolventQuadraticOn T hP hSelf y)
      (Set.Iio G.mass) lambda :=
  (G.vacuumOrthogonalRealResolventQuadraticOn_orderCertificate
    T hP hSelf y).2.2 lambda hlambda

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end MathlibAnalytic
end MGAP4D

end
