import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullGraphApproximation
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

/-- The difference between the bounded rescaled-defect graph point and its
closed continuum Hamiltonian graph point converges strongly to zero. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_graph_error_tendsto_zero
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
        (xTau,
            T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
              hInnerSymmetric tau.1 xTau) -
          ((x : P.VacuumOrthogonalHilbert),
            T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x))
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  simpa using
    (G.admissibleRescaledDefect_graph_tendsto_continuumGraphPoint
      T hP hInnerSymmetric hSelf hlambda x).sub tendsto_const_nhds

/-- Equivalently, the product-Hilbert norm of the full graph error tends to
zero.  This is the norm-form graph approximation needed for later closed-
operator and spectral convergence arguments. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefect_graph_error_norm_tendsto_zero
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
        ‖(xTau,
              T.toPhysicalSemigroup.vacuumOrthogonalRescaledDefect
                hInnerSymmetric tau.1 xTau) -
            ((x : P.VacuumOrthogonalHilbert),
              T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)‖)
      G.admissibleRescaledDefectTimeFilter
      (𝓝 0) := by
  simpa using
    (G.admissibleRescaledDefect_graph_error_tendsto_zero
      T hP hInnerSymmetric hSelf hlambda x).norm

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
