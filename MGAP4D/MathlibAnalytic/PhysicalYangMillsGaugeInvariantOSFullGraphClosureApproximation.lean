import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSAdmissibleRescaledDefectTimeFilter
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

/-- Every point of the closed continuum excitation-Hamiltonian graph belongs
to the closure of the range of bounded rescaled-defect graph approximants. -/
theorem VacuumSemigroupGapSlope.continuumGraphPoint_mem_closure_admissibleRescaledDefectGraphRange
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    ((x : P.VacuumOrthogonalHilbert),
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x) ∈
      closure
        (Set.range fun tau : G.AdmissibleRescaledDefectTime =>
          let xTau :=
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda
              ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
                lambda x)
          (xTau,
            T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric tau.1 xTau)) := by
  letI : G.admissibleRescaledDefectTimeFilter.NeBot :=
    G.admissibleRescaledDefectTimeFilter_neBot T
  exact mem_closure_of_tendsto
    (G.admissibleRescaledDefect_graph_tendsto_continuumGraphPoint
      T hP hInnerSymmetric hSelf hlambda x)
    (Eventually.of_forall fun tau => ⟨tau, rfl⟩)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
