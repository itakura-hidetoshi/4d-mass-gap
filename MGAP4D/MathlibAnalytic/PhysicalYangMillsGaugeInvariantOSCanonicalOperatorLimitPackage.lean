import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongResolvent
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventPowers
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalMixedResolventProductLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventAlgebra
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventIdentity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventThreePointDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventThreePointLagrange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventWordPermutation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSOperatorGraphKuratowskiCanonicalFilter
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Canonical finite-time operator convergence package on the admissible
positive small-time filter.  It combines pointwise strong convergence of every
below-gap real resolvent with equality of both Painlevé–Kuratowski graph limits
and the graph of the closed continuum excitation Hamiltonian. -/
theorem VacuumSemigroupGapSlope.canonicalRescaledDefectOperatorLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) :
    (∀ {lambda : ℝ} (hlambda : lambda < G.mass / 2),
      ∀ y : P.VacuumOrthogonalHilbert,
        Tendsto
          (fun tau : G.AdmissibleRescaledDefectTime =>
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda y)
          G.admissibleRescaledDefectTimeFilter
          (𝓝
            (G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y))) ∧
    (FilterSet.kuratowskiInnerLimit G.admissibleRescaledDefectTimeFilter
          (G.rescaledDefectGraphFamily T hInnerSymmetric
            (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
        G.continuumHamiltonianGraph T hSelf ∧
      FilterSet.kuratowskiOuterLimit G.admissibleRescaledDefectTimeFilter
          (G.rescaledDefectGraphFamily T hInnerSymmetric
            (fun tau : G.AdmissibleRescaledDefectTime => tau)) =
        G.continuumHamiltonianGraph T hSelf) := by
  constructor
  · intro lambda hlambda y
    exact
      G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
        T hP hInnerSymmetric hSelf hlambda y
  · exact
      G.canonicalFilter_rescaledDefectGraph_kuratowskiLimits_eq_continuumHamiltonianGraph
        T hP hInnerSymmetric hSelf

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
