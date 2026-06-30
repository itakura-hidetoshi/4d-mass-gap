import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSExactShiftedDefectGraphFamily
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

theorem VacuumSemigroupGapSlope.exactShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {ι : Type*} (l : Filter ι) [NeBot l]
    {lambdaNet : ι → ℝ} {lambda : ℝ}
    (hlambda : lambda < G.mass / 2)
    {yNet : ι → P.VacuumOrthogonalHilbert}
    {y : P.VacuumOrthogonalHilbert}
    {tau : ι → G.AdmissibleRescaledDefectTime}
    (hTau : Tendsto tau l G.admissibleRescaledDefectTimeFilter)
    (hLambda : Tendsto lambdaNet l (nhds lambda))
    (hy : Tendsto yNet l (nhds y)) :
    FilterSet.kuratowskiInnerLimit l
        (G.exactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} ∧
    FilterSet.kuratowskiOuterLimit l
        (G.exactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet) =
      {(G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda y,
        T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf
          (G.vacuumOrthogonalContinuumRealResolventDomainPoint
            T hP hInnerSymmetric hSelf hlambda y))} := by
  have hFamily :
      G.exactShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet =
        G.approximateShiftedDefectGraphFamily
          T hInnerSymmetric tau lambdaNet yNet (fun _ => 0) := by
    funext i
    exact G.exactShiftedDefectGraphFamily_eq_zeroTolerance
      T hInnerSymmetric tau lambdaNet yNet i
  rw [hFamily]
  exact G.zeroToleranceShiftedDefectGraphFamily_kuratowskiLimits_eq_singleton
    T hP hInnerSymmetric hSelf l hlambda hTau hLambda hy

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
