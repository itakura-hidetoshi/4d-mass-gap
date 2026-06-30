import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullGraphNormApproximation
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

/-- The standard sum-form graph error of the bounded rescaled defects tends to
zero at every point of the closed continuum Hamiltonian graph. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_graph_sum_norm_tendsto_zero
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        let xTau :=
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda
            ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
              lambda x)
        ‖xTau - (x : P.VacuumOrthogonalHilbert)‖ +
          ‖T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric tau.1 xTau -
            T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x‖)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  have hxError :=
    (G.admissibleRescaledDefectResolvent_tendsto_continuumDomain
      T hP hInnerSymmetric hSelf hlambda x).sub_const
        (x : P.VacuumOrthogonalHilbert)
  have hHamiltonianError :=
    (G.admissibleRescaledDefect_apply_resolvent_tendsto_closedRightHamiltonian
      T hP hInnerSymmetric hSelf hlambda x).sub_const
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)
  simpa using hxError.norm.add hHamiltonianError.norm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
