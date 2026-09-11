import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullGraphRangeClosure
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

/-- Every strong sequential limit of graph points of the closed excitation
Hamiltonian is again a graph point of that Hamiltonian. -/
theorem vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_graph_limit_mem
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {u : ℕ → (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain}
    {x eta : P.VacuumOrthogonalHilbert}
    (hu : Tendsto (fun n => (u n : P.VacuumOrthogonalHilbert)) atTop (nhds x))
    (hHu : Tendsto
      (fun n => T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf (u n))
      atTop (nhds eta)) :
    ∃ xDomain : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain,
      (xDomain : P.VacuumOrthogonalHilbert) = x ∧
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf xDomain = eta := by
  let A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
  have hPair :
      Tendsto
        (fun n => ((u n : P.VacuumOrthogonalHilbert), A (u n)))
        atTop
        (nhds (x, eta)) := by
    simpa [A] using hu.prodMk_nhds hHu
  have hGraph : (x, eta) ∈ (A.graph : Set (P.VacuumOrthogonalHilbert × P.VacuumOrthogonalHilbert)) :=
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isClosed hP hSelf).mem_of_tendsto
      hPair
      (Eventually.of_forall fun n => by
        exact (LinearPMap.mem_graph_iff A).2 ⟨u n, rfl, rfl⟩)
  exact (LinearPMap.mem_graph_iff A).1 hGraph

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
