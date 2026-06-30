import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullGraphClosureApproximation
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

/-- The full graph of the closed continuum excitation Hamiltonian is contained
in the closure of the joint range of all resolvent-selected bounded
rescaled-defect graph approximants. -/
theorem VacuumSemigroupGapSlope.continuumGraphRange_subset_closure_jointAdmissibleRescaledDefectGraphRange
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < G.mass / 2) :
    Set.range
        (fun x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain =>
          ((x : P.VacuumOrthogonalHilbert),
            T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)) ⊆
      closure
        (Set.range
          (fun z :
              (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain ×
                G.AdmissibleRescaledDefectTime =>
            let x := z.1
            let tau := z.2
            let xTau :=
              G.admissibleRescaledDefectResolvent
                hInnerSymmetric tau hlambda
                ((T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).realShift
                  lambda x)
            (xTau,
              T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric tau.1 xTau))) := by
  rintro p ⟨x, rfl⟩
  apply closure_mono ?_
    (G.continuumGraphPoint_mem_closure_admissibleRescaledDefectGraphRange
      T hP hInnerSymmetric hSelf hlambda x)
  rintro q ⟨tau, rfl⟩
  exact ⟨(x, tau), rfl⟩

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
