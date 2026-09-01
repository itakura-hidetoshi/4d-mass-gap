import MGAP4D.MathlibAnalytic.LinearPMapHasCoreOfGraphApproximation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalCoreGraphApproximation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalSelfAdjoint
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

/-- The canonical vacuum-orthogonal right-Hamiltonian core is a genuine
Mathlib operator core for the graph-closed physical excitation Hamiltonian.

The nontrivial analytic input is the already-proved graph approximation by
vacuum-corrected right-generator vectors.  The abstract graph-core criterion
then turns that sequence-level statement into the exact closure identity
`(A.domRestrict C).closure = A`. -/
theorem vacuumOrthogonalClosedRightHamiltonian_hasCore_rightHamiltonianCore
    (T : P.StronglyContinuousPhysicalSemigroup)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric) :
    let hClosedSymmetric :=
      T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hInnerSymmetric
    (T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric).HasCore
      T.vacuumOrthogonalRightHamiltonianCoreDomain := by
  let hClosedSymmetric :=
    T.closedRightHamiltonian_isFormalAdjoint_of_innerSymmetric hInnerSymmetric
  let A : P.VacuumOrthogonalHilbert →ₗ.[ℝ] P.VacuumOrthogonalHilbert :=
    T.vacuumOrthogonalClosedRightHamiltonian hClosedSymmetric
  let C : Submodule ℝ P.VacuumOrthogonalHilbert :=
    T.vacuumOrthogonalRightHamiltonianCoreDomain
  have hC : C ≤ A.domain := by
    intro x hx
    let c : T.vacuumOrthogonalRightHamiltonianCoreDomain := ⟨x, hx⟩
    change x ∈ T.vacuumOrthogonalClosedRightHamiltonianDomain
    exact (T.vacuumOrthogonalRightHamiltonianCoreClosedDomainPoint c).property
  have hAmbientSelf : IsSelfAdjoint T.closedRightHamiltonian :=
    T.closedRightHamiltonian_isSelfAdjoint_of_isFormalAdjoint hClosedSymmetric
  have hAClosed : A.IsClosed := by
    have hClosed :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isClosed
        hP hAmbientSelf
    simpa only [A, vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using hClosed
  apply realLinearPMap_hasCore_of_seq_graph_approximation A C hC hAClosed
  intro x
  obtain ⟨u, huBase, huValue⟩ :=
    T.exists_vacuumOrthogonalRightHamiltonianCore_graph_approximation
      hP hInnerSymmetric x
  refine ⟨u, huBase, ?_⟩
  simpa only [A, hClosedSymmetric, C] using huValue

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
